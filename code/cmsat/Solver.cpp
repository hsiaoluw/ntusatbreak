/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2009, Niklas Sorensson
Copyright (c) 2009-2012, Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "cmsat/Solver.h"
#include <cmath>
#include <string.h>
#include <algorithm>
#include <limits.h>
#include <vector>
#include <iomanip>
#include <algorithm>

#include "cmsat/Clause.h"
#include "cmsat/time_mem.h"

#include "cmsat/VarReplacer.h"
#include "cmsat/XorFinder.h"
#include "cmsat/ClauseCleaner.h"
#include "cmsat/RestartTypeChooser.h"
#include "cmsat/FailedLitSearcher.h"
#include "cmsat/Subsumer.h"
#include "cmsat/XorSubsumer.h"
#include "cmsat/StateSaver.h"
#include "cmsat/SCCFinder.h"
#include "cmsat/SharedData.h"
#include "cmsat/ClauseVivifier.h"
//#include "cmsat/Gaussian.h"
#include "cmsat/MatrixFinder.h"
#include "cmsat/DataSync.h"
#include "cmsat/BothCache.h"
#include "cmsat/EnhanceGaussian.h"   // include by hankf4

#ifdef VERBOSE_DEBUG
#define UNWINDING_DEBUG
#endif

//#define DEBUG_UNCHECKEDENQUEUE_LEVEL0
//#define VERBOSE_DEBUG_POLARITIES
//#define DEBUG_DYNAMIC_RESTART
//#define UNWINDING_DEBUG

//**********************************
// Constructor/Destructor:
//**********************************

using namespace CMSat;

/**
@brief Sets a sane default config and allocates handler classes
*/
Solver::Solver(const SolverConf& _conf, const GaussConf& _gaussconfig, SharedData* sharedData) :
        // Parameters: (formerly in 'SearchParams')
        conf(_conf)
        , gaussconfig(_gaussconfig)
        , needToInterrupt  (false)
        
		#ifdef USE_GAUSS
		,Total_gauss_time(0)
		,debug_call(0)
		,big_gaussnum(0) // add by hankf4
		,big_propagate(0)
		,big_conflict(0)
		,engaus_disable(false)
		,Is_Gauss_first(false)
		,EnhancGauss_matrixes_size(0)  // add by hankf4
		,gauss_called(false)
		,gauss_learn_size(0)
		, sum_unit(0)
		, init_sum_unit(0)
		,sum_Enpropagate(0)
		,sum_Enconflict(0)
		,sum_Enpropagate_two(0)
		,sum_Enconflict_two(0)
		,sum_En_el_propagate(0)
		,sum_En_el_conflict(0)
		,sum_En_el_propagate_two(0)
		,sum_En_el_conflict_two(0)
		,sum_Encalled(0)
		,sum_Encalled_eliminate(0)
		,sum_already_true(0)
		,sum_el_already_true(0)
		,sum_already_true_stop(0)
		,sum_gauss_time((double)0)
		
        , sum_gauss_called (0)
        , sum_gauss_confl  (0)
        , sum_gauss_prop   (0)
        , sum_gauss_unit_truths (0)
		, lackxor   (0)
        #endif //USE_GAUSS
        // Stats
        , starts(0), dynStarts(0), staticStarts(0), fullStarts(0)
		, staticStarts_ori_last(0),staticStarts_ori(0) // add by alanwang
		, decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
        , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
        , nbGlue2(0), numNewBin(0), lastNbBin(0), lastSearchForBinaryXor(0), nbReduceDB(0)
        , improvedClauseNo(0), improvedClauseSize(0)
        , numShrinkedClause(0), numShrinkedClauseLits(0)
        , moreRecurMinLDo(0)
        , updateTransCache(0)
        , nbClOverMaxGlue(0)

        , ok               (true)
        , numBins          (0)
        , cla_inc          (1)
        , qhead            (0)
        , mtrand           ((unsigned long int)0)

        //variables
        , order_heap       (VarOrderLt(activity))
        , var_inc          (128)

        //learnts
        , numCleanedLearnts(1)
        , nbClBeforeRed    (NBCLAUSESBEFOREREDUCE)
        , nbCompensateSubsumer (0)
        , libraryCNFFile   (NULL)
        , restartType      (static_restart)
        , lastSelectedRestartType (static_restart)
        , simplifying      (false)
        , totalSimplifyTime(0.0)
        , simpDB_assigns   (-1)
        , simpDB_props     (0)
		/// add by alanwang
		, additional_xor   (0) //add by alanwang
		, additional_three (0) //add by alanwang
		, additional_two   (0) //add by alanwang
		, additional_one   (0) //add by alanwang
		, additional_one_last(0) //add by alanwang
		, additional_morexor (0)
		, additional_morexorlast2(0)
		, additional_morexorlast(0)
		//, additional_mut		(0)
		//, additional_mut_ori    (0)
		, morexortime			(0)
		, lockstat				(0)
		, dopurenow				(false)
		, dopuretimes			(0)
		, constructpure         (false)
		, num_pureliteral		(0)
		, first					(true)
		, num_purelearnt		(0)
		, dopuretime			(0)
		, chead					(0)
		/// ---end add
		
#ifdef HAVE_MYSQL
        , mysqClauseNum    (0)
#endif //HAVE_MYSQL
{
    mtrand.seed(conf.origSeed);
    //#ifdef ENABLE_UNWIND_GLUE
    //assert(conf.maxGlue < MAX_THEORETICAL_GLUE);
   // #endif //ENABLE_UNWIND_GLUE
    varReplacer = new VarReplacer(*this);
    clauseCleaner = new ClauseCleaner(*this);
    failedLitSearcher = new FailedLitSearcher(*this);
    subsumer = new Subsumer(*this);
    xorSubsumer = new XorSubsumer(*this);
    restartTypeChooser = new RestartTypeChooser(*this);
    sCCFinder = new SCCFinder(*this);
    clauseVivifier = new ClauseVivifier(*this);
    matrixFinder = new MatrixFinder(*this);

    if (sharedData)
        dataSync = new DataSync(*this, sharedData);
    else
        dataSync = NULL;

		
	getinfoAlready.clear();
	clauses_cpy.clear();
	if(nClauses()<70000) additional_mut_ori=5;
	else additional_mut_ori=5;
	
	clauseAllocator.ssolver=this;
	additional_mut=additional_mut_ori;
	//clauseAllocator.solver=this;
	//clauses_cpy.clear();
	
	litcontain=NULL;
	puresatby=NULL;	
		
		
		
		
		
    #ifdef HAVE_MYSQL
    //Init SQL
    insSTMTLits.STMT = NULL;
    insSTMTCl.STMT = NULL;
    if (conf.serverConn) {
        initMySQLStatements();
    }
    #endif
}

#ifdef HAVE_MYSQL
void Solver::initMySQLStatements()
{
    // Prepare an INSERT query with 2 parameters
    insSTMTLits.STMT = mysql_stmt_init(conf.serverConn);
    if (!insSTMTLits.STMT) {
        std::cout << "Error: mysql_stmt_init() out of memory" << std::endl;
        exit(1);
    }

    const char* STMTTxt = "insert into literals(clindex,var,inv) values(?,?,?)";
    if (mysql_stmt_prepare(insSTMTLits.STMT, STMTTxt, strlen(STMTTxt))) {
        std::cout << "Error in mysql_stmt_prepare(), INSERT failed" << std::endl
        << mysql_stmt_error(insSTMTLits.STMT) << std::endl;
        exit(0);
    }
    std::cout << "prepare INSERT successful" << std::endl;

    /* Get the parameter count from the statement */
    int param_count = mysql_stmt_param_count(insSTMTLits.STMT);
    if (param_count != 3) { // validate parameter count
        std::cout << "invalid parameter count returned by MySQL" << std::endl;
        exit(1);
    }

    memset(insSTMTLits.bind, 0, sizeof(insSTMTLits.bind));

    //Bind parameters
    insSTMTLits.bind[0].buffer_type= MYSQL_TYPE_LONG;
    insSTMTLits.bind[0].buffer= (char *)&insSTMTLits.autoInc;
    insSTMTLits.bind[0].is_null= 0;
    insSTMTLits.bind[0].length= 0;

    insSTMTLits.bind[1].buffer_type= MYSQL_TYPE_LONG;
    insSTMTLits.bind[1].buffer= (char *)&insSTMTLits.litVar;
    insSTMTLits.bind[1].is_null= 0;
    insSTMTLits.bind[1].length= 0;

    insSTMTLits.bind[2].buffer_type= MYSQL_TYPE_SHORT;
    insSTMTLits.bind[2].buffer= (char *)&insSTMTLits.inverted;
    insSTMTLits.bind[2].is_null= 0;
    insSTMTLits.bind[2].length= 0;

    // Bind the buffers
    if (mysql_stmt_bind_param(insSTMTLits.STMT, insSTMTLits.bind)) {
        std::cout << "mysql_stmt_bind_param() failed" << std::endl
        << mysql_stmt_error(insSTMTLits.STMT) << std::endl;
        exit(1);
    }

    insSTMTCl.STMT = mysql_stmt_init(conf.serverConn);
    if (!insSTMTCl.STMT) {
        std::cout << "Error: mysql_stmt_init() out of memory" << std::endl;
        exit(1);
    }
    const char* STMTTxt2 = "insert into clauses(runno, declevel, traillevel, glue, size, num, learnt) values(?,?,?,?,?,?,?)";
    if (mysql_stmt_prepare(insSTMTCl.STMT, STMTTxt2, strlen(STMTTxt2))) {
        std::cout << "Error in mysql_stmt_prepare(), INSERT failed" << std::endl
        << mysql_stmt_error(insSTMTCl.STMT) << std::endl;
        exit(0);
    }
    std::cout << "prepare INSERT successful" << std::endl;

    /* Get the parameter count from the statement */
    param_count = mysql_stmt_param_count(insSTMTCl.STMT);
    if (param_count != 7) { // validate parameter count
        std::cout << "invalid parameter count returned by MySQL" << std::endl;
        exit(1);
    }

    memset(insSTMTCl.bind, 0, sizeof(insSTMTCl.bind));

    //Add main parameters of the clause
    insSTMTCl.bind[0].buffer_type= MYSQL_TYPE_LONG;
    insSTMTCl.bind[0].buffer= (char *)&insSTMTCl.runNo;
    insSTMTCl.bind[0].buffer_type= MYSQL_TYPE_LONG;
    insSTMTCl.bind[0].buffer= (char *)&insSTMTCl.runNo;
    insSTMTCl.bind[0].is_null= 0;
    insSTMTCl.bind[0].length= 0;

    insSTMTCl.bind[1].buffer_type= MYSQL_TYPE_LONG;
    insSTMTCl.bind[1].buffer= (char *)&insSTMTCl.decLevel;
    insSTMTCl.bind[1].is_null= 0;
    insSTMTCl.bind[1].length= 0;

    insSTMTCl.bind[2].buffer_type= MYSQL_TYPE_LONG;
    insSTMTCl.bind[2].buffer= (char *)&insSTMTCl.trailLevel;
    insSTMTCl.bind[2].is_null= 0;
    insSTMTCl.bind[2].length= 0;

    insSTMTCl.bind[3].buffer_type= MYSQL_TYPE_LONG;
    insSTMTCl.bind[3].buffer= (char *)&insSTMTCl.glue;
    insSTMTCl.bind[3].is_null= 0;
    insSTMTCl.bind[3].length= 0;

    insSTMTCl.bind[4].buffer_type= MYSQL_TYPE_LONG;
    insSTMTCl.bind[4].buffer= (char *)&insSTMTCl.size;
    insSTMTCl.bind[4].is_null= 0;
    insSTMTCl.bind[4].length= 0;

    insSTMTCl.bind[5].buffer_type= MYSQL_TYPE_LONG;
    insSTMTCl.bind[5].buffer= (char *)&insSTMTCl.num;
    insSTMTCl.bind[5].is_null= 0;
    insSTMTCl.bind[5].length= 0;

    insSTMTCl.bind[6].buffer_type= MYSQL_TYPE_SHORT;
    insSTMTCl.bind[6].buffer= (char *)&insSTMTCl.learnt;
    insSTMTCl.bind[6].is_null= 0;
    insSTMTCl.bind[6].length= 0;

    // Bind the buffers
    if (mysql_stmt_bind_param(insSTMTCl.STMT, insSTMTCl.bind)) {
        std::cout << "mysql_stmt_bind_param() failed" << std::endl
        << mysql_stmt_error(insSTMTCl.STMT) << std::endl;
        exit(1);
    }

    //Inserting element into solverruns to get unique ID
    if (mysql_query(conf.serverConn, "INSERT INTO solverruns VALUES()")) {
        std::cout << "Couldn't insert into table 'solverruns'" << std::endl;
        exit(1);
    }

    insSTMTCl.runNo = mysql_insert_id(conf.serverConn);
    std::cout << "This run number is: " << insSTMTCl.runNo << std::endl;
}
#endif //HAVE_MYSQL

/**
@brief Frees clauses and frees all allocated hander classes
*/
Solver::~Solver()
{
    //clearGaussMatrixes(); clear by alanwang
	clearEnGaussMatrixes(); // add by alanwang
    delete matrixFinder;
    delete varReplacer;
    delete clauseCleaner;
    delete failedLitSearcher;
    delete subsumer;
    delete xorSubsumer;
    delete restartTypeChooser;

	if(litcontain!=NULL)
	  { delete [] litcontain;
	  litcontain=NULL;}
	   
	if (puresatby !=NULL)
		{delete []  puresatby;
		 puresatby=NULL;
		}
		
    if (libraryCNFFile)
        fclose(libraryCNFFile);

#ifdef HAVE_MYSQL
    if (conf.serverConn && insSTMTLits.STMT) {
        if (mysql_stmt_close(insSTMTLits.STMT)) {
            std::cout << "c failed while closing the statement"
            << mysql_stmt_error(insSTMTLits.STMT) << std::endl;
            exit(1);
        }

        if (mysql_stmt_close(insSTMTCl.STMT)) {
            std::cout << "c failed while closing the statement"
            << mysql_stmt_error(insSTMTCl.STMT) << std::endl;
            exit(1);
        }
    }
#endif
}

//**********************************
// Minor methods
//**********************************

/**
@brief Creates a new SAT variable in the solver

This entails making the datastructures large enough to fit the new variable
in all internal datastructures as well as all datastructures used in
classes used inside Solver

@p dvar The new variable should be used as a decision variable?
   NOTE: this has effects on the meaning of a SATISFIABLE result
*/
Var Solver::newVar(bool dvar) throw (std::out_of_range)
{
    Var v = nVars();
    if (v >= 1<<30)
        throw std::out_of_range("ERROR! Variable requested is far too large");
	GausWatches.push(); // add by hankf4
	
	
    watches   .push();          // (list for positive literal)
    watches   .push();          // (list for negative literal)
    reason    .push(PropBy());
    assigns   .push(l_Undef);
    level     .push(-1);
    binPropData.push();
    activity  .push(0);
    seen      .push_back(0);
    seen      .push_back(0);
	candopure .push(true);
    #ifdef ENABLE_UNWIND_GLUE
    unWindGlue.push(NULL);
    #endif //ENABLE_UNWIND_GLUE

    //Transitive OTF self-subsuming resolution
    seen2     .push_back(0);
    seen2     .push_back(0);
    litReachable.push_back(LitReachData());
    litReachable.push_back(LitReachData());
    transOTFCache.push_back(TransCache());
    transOTFCache.push_back(TransCache());


    polarity  .push_back(defaultPolarity());

    decision_var.push_back(dvar);
    insertVarOrder(v);

    varReplacer->newVar();
    if (nVars() > conf.switch_off_subsumer_max_vars) {
        delete subsumer;
        subsumer = NULL;
    }

    if (subsumer)
        subsumer->newVar();

    xorSubsumer->newVar();

    if (dataSync)
        dataSync->newVar();

    insertVarOrder(v);

    if (libraryCNFFile)
        fprintf(libraryCNFFile, "c Solver::newVar() called\n");

    return v;
}

/**
@brief Adds an xor clause to the problem

Should ONLY be called from internally. This is different from the extenal
xor clause-adding function addXorClause() in that it assumes that the variables
inside are decision variables, have not been replaced, eliminated, etc.
*/
template<class T>
XorClause* Solver::addXorClauseInt(T& ps, bool xorEqualFalse, const bool learnt) throw (std::out_of_range)
{
    //assert(qhead == trail.size());
   // assert(decisionLevel() == 0);

    if (ps.size() > (0x01UL << 18))
        throw std::out_of_range("c Too long clause!");
    std::sort(ps.getData(), ps.getDataEnd());
    Lit p;
    uint32_t i, j;
    for (i = j = 0, p = lit_Undef; i != ps.size(); i++) {
        if (ps[i].var() == p.var()) {
            //added, but easily removed
            j--;
            p = lit_Undef;
            if (!assigns[ps[i].var()].isUndef())
                xorEqualFalse ^= assigns[ps[i].var()].getBool();
        } else if (assigns[ps[i].var()].isUndef()) { //just add
            ps[j++] = p = ps[i];
            //assert(!subsumer || !subsumer->getVarElimed()[p.var()]);
            //assert(!xorSubsumer->getVarElimed()[p.var()]);
        } else //modify xorEqualFalse instead of adding
            xorEqualFalse ^= (assigns[ps[i].var()].getBool());
    }
    ps.shrink(i - j);

    switch(ps.size()) {
        case 0: {
            if (!xorEqualFalse) ok = false;
            return NULL;
        }
        case 1: {
            uncheckedEnqueue(Lit(ps[0].var(), xorEqualFalse));
            ok = (propagate<false>().isNULL());
            return NULL;
        }
        case 2: {
            #ifdef VERBOSE_DEBUG
            cout << "--> xor is 2-long, replacing var " << ps[0].var()+1 << " with " << (!xorEqualFalse ? "-" : "") << ps[1].var()+1 << endl;
            #endif

            ps[0] = ps[0].unsign();
            ps[1] = ps[1].unsign();
            varReplacer->replace(ps, xorEqualFalse, learnt);
            return NULL;
        }
        default: {
            //assert(!learnt);
            XorClause* c = clauseAllocator.XorClause_new(ps, xorEqualFalse);
            attachClause(*c);
            return c;
        }
    }
}

template XorClause* Solver::addXorClauseInt(vec<Lit>& ps, bool xorEqualFalse, const bool learnt);
template XorClause* Solver::addXorClauseInt(XorClause& ps, bool xorEqualFalse, const bool learnt);

/**
@brief Adds an xor clause to the problem

Calls addXorClauseInt() for the heavy-lifting. Basically, this does a bit
of debug-related stuff (see "libraryCNFFile"), and then checks if any of the
variables have been eliminated, replaced, etc. If so, it treats it correctly,
and then calls addXorClauseInt() to actually add the xor clause.

@p ps[inout] The VARIABLES in the xor clause. Beware, there must be NO signs
            here: ALL must be unsigned (.sign() == false). Values passed here
            WILL be changed, ordered, removed, etc!
@p xorEqualFalse The xor must be equal to TRUE or false?
*/
template<class T>
bool Solver::addXorClause(T& ps, bool xorEqualFalse) throw (std::out_of_range)
{
    //assert(decisionLevel() == 0);
    if (ps.size() > (0x01UL << 18))
        throw std::out_of_range("Too long clause!");

    if (libraryCNFFile) {
        fprintf(libraryCNFFile, "x");
        for (uint32_t i = 0; i < ps.size(); i++) ps[i].print(libraryCNFFile);
        fprintf(libraryCNFFile, "0\n");
    }

    //Flip signs accordingly
   /* for(size_t i = 0; i < ps.size(); i++) {
        if (ps[i].sign()) {
            ps[i] = ps[i].unsign();
            xorEqualFalse ^= true;
        }
    }*/

    if (!ok)
        return false;
   // assert(qhead == trail.size());
   // #ifndef NDEBUG
    //for (Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
   //     assert(l->var() < nVars() && "Clause inserted, but variable inside has not been declared with newVar()!");
   // }
   // #endif

    if (varReplacer->getNumLastReplacedVars()
        || (subsumer && subsumer->getNumElimed())
        || xorSubsumer->getNumElimed()
    ) {
        for (uint32_t i = 0; i != ps.size(); i++) {
            Lit otherLit = varReplacer->getReplaceTable()[ps[i].var()];
            if (otherLit.var() != ps[i].var()) {
                ps[i] = Lit(otherLit.var(), false);
                xorEqualFalse ^= otherLit.sign();
            }
            if (subsumer && subsumer->getVarElimed()[ps[i].var()] && !subsumer->unEliminate(ps[i].var()))
                return false;

            else if (xorSubsumer->getVarElimed()[ps[i].var()] && !xorSubsumer->unEliminate(ps[i].var()))
                return false;
        }
    }

    XorClause* c = addXorClauseInt(ps, xorEqualFalse);
    if (c != NULL){
		xorclauses.push(c);
		if(conf.doPureliteral){
					for(uint32_t ii=0;ii< c->size();ii++)
					{
					
						candopure[(*c)[ii].var()]=false;
						if(constructpure){
						if(litcontain[(*c)[ii].toInt()].size()>0)
						{
						  vec<uint32_t>& ll 		   = litcontain[(*c)[ii].toInt()];
						  vec<uint32_t>& ww            = watch_c[ll[0]];
						  uint32_t m=0;
						  uint32_t k=0;
						  for(;k<ww.size();k++)
						  {
							 if(ww[k]!=(*c)[ii].toInt()) ww[m++]=ww[k];
						  }
						  ww.shrink_(k-m);
						}
						litcontain[(*c)[ii].toInt()].clear();
						
						if(litcontain[(~(*c)[ii]).toInt()].size()>0)
						{
						  vec<uint32_t>& ll 		   = litcontain[(~(*c)[ii]).toInt()];
						  vec<uint32_t>& ww            = watch_c[ll[0]];
						  uint32_t m=0;
						  uint32_t k=0;
						  for(;k<ww.size();k++)
						  {
							 if(ww[k]!=(~(*c)[ii]).toInt()) ww[m++]=ww[k];
						  }
						  ww.shrink_(k-m);
						}
						litcontain[(~(*c)[ii]).toInt()].clear();
						}
					}
			}
	}

    return ok;
}

template bool Solver::addXorClause(vec<Lit>& ps, bool xorEqualFalse);
template bool Solver::addXorClause(XorClause& ps, bool xorEqualFalse);

/**
@brief Adds a clause to the problem. Should ONLY be called internally

This code is very specific in that it must NOT be called with varibles in
"ps" that have been replaced, eliminated, etc. Also, it must not be called
when the solver is in an UNSAT (!ok) state, for example. Use it carefully,
and only internally
*/
template <class T>
Clause* Solver::addClauseInt(T& ps
                            , const bool learnt, const uint32_t glue, const float miniSatActivity
                            , const bool inOriginalInput)
{
    //assert(ok);
/*#ifdef VERBOSE_DEBUG
    std::cout << "Adding new clause: " << std::endl;
    for(size_t i = 0; i< ps.size(); i++) {
        printLit(ps[i]);
        std::cout << " ";
    }
    std::cout << std::endl;
#endif //VERBOSE_DEBUG*/

if(conf.doPureliteral) {
		if (varReplacer->getNumLastReplacedVars() || (subsumer&&subsumer->getNumElimed()) || xorSubsumer->getNumElimed()) {
			for (uint32_t i = 0; i != ps.size(); i++) {
				ps[i] = varReplacer->getReplaceTable()[ps[i].var()] ^ ps[i].sign();
				if (subsumer&&subsumer->getVarElimed()[ps[i].var()] && !subsumer->unEliminate(ps[i].var()))
					return NULL;
				if (xorSubsumer->getVarElimed()[ps[i].var()] && !xorSubsumer->unEliminate(ps[i].var()))
					return NULL;
			}
		}
	}



    std::sort(ps.getData(), ps.getDataEnd());
    Lit p = lit_Undef;
    uint32_t i, j;
    for (i = j = 0; i != ps.size(); i++) {
        if (value(ps[i]).getBool() || ps[i] == ~p)
            return NULL;
        else if (value(ps[i]) != l_False && ps[i] != p) {
            ps[j++] = p = ps[i];
            //assert(!subsumer || !subsumer->getVarElimed()[p.var()]);
            //assert(!xorSubsumer->getVarElimed()[p.var()]);
        }
    }
    ps.shrink(i - j);

    if (ps.size() == 0) {
        ok = false;
        return NULL;
    } else if (ps.size() == 1) {
        uncheckedEnqueue(ps[0]);
        ok = (propagate<false>().isNULL());
        return NULL;
    }

    if (ps.size() > 2) {
        Clause* c = clauseAllocator.Clause_new(ps);
        if (learnt) c->makeLearnt(glue, miniSatActivity);
        attachClause(*c);
        return c;
    } else {
        attachBinClause(ps[0], ps[1], learnt);
        if (dataSync && !inOriginalInput)
            dataSync->signalNewBinClause(ps);
        numNewBin++;
        return NULL;
    }
}

template Clause* Solver::addClauseInt(Clause& ps, const bool learnt, const uint32_t glue, const float miniSatActivity, const bool inOriginalInput);
template Clause* Solver::addClauseInt(vec<Lit>& ps, const bool learnt, const uint32_t glue, const float miniSatActivity, const bool inOriginalInput);

template<class T> bool Solver::addClauseHelper(T& ps) throw (std::out_of_range)
{
    //assert(decisionLevel() == 0);
    if (ps.size() > (0x01UL << 18))
        throw std::out_of_range("Too long clause!");

    if (libraryCNFFile) {
        for (uint32_t i = 0; i != ps.size(); i++) ps[i].print(libraryCNFFile);
        fprintf(libraryCNFFile, "0\n");
    }

    if (!ok) return false;
    //assert(qhead == trail.size());
    //#ifndef NDEBUG
   // for (Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
    //    assert(l->var() < nVars() && "Clause inserted, but variable inside has not been declared with Solver::newVar() !");
    //}
    //#endif

    // Check if clause is satisfied and remove false/duplicate literals:
    if (varReplacer->getNumLastReplacedVars()
        || (subsumer && subsumer->getNumElimed())
        || xorSubsumer->getNumElimed()
    ) {
        for (uint32_t i = 0; i != ps.size(); i++) {
            ps[i] = varReplacer->getReplaceTable()[ps[i].var()] ^ ps[i].sign();

            if (subsumer && subsumer->getVarElimed()[ps[i].var()] && !subsumer->unEliminate(ps[i].var()))
                return false;

            if (xorSubsumer->getVarElimed()[ps[i].var()] && !xorSubsumer->unEliminate(ps[i].var()))
                return false;
        }
    }

    for (uint32_t i = 0; i < ps.size(); i++) {
        std::swap(ps[i], ps[(mtrand.randInt() % (ps.size()-i)) + i]);
    }

    return true;
}


/**
@brief Adds a clause to the problem. Calls addClauseInt() for heavy-lifting

Does some debug-related stuff (see "libraryCNFFile"), and checks whether the
variables of the literals in "ps" have been eliminated/replaced etc. If so,
it acts on them such that they are correct, and calls addClauseInt() to do
the heavy-lifting
*/
template<class T>
bool Solver::addClause(T& ps)
{
    #ifdef VERBOSE_DEBUG
    std::cout << "addClause() called with new clause: " << ps << std::endl;
    #endif //VERBOSE_DEBUG
    if (!addClauseHelper(ps)) return false;
    Clause* c = addClauseInt(ps, false, 0, 0, true);
    if (c != NULL) clauses.push(c);

    return ok;
}

template bool Solver::addClause(vec<Lit>& ps);
template bool Solver::addClause(Clause& ps);


template<class T>
bool Solver::addLearntClause(T& ps, const uint32_t glue, const float miniSatActivity)
{
    if (!addClauseHelper(ps)) return false;
    Clause* c = addClauseInt(ps, true, glue, miniSatActivity, true);
    if (c != NULL) learnts.push(c);

    return ok;
}

template bool Solver::addLearntClause(vec<Lit>& ps, const uint32_t glue, const float miniSatActivity);
template bool Solver::addLearntClause(Clause& ps, const uint32_t glue, const float miniSatActivity);


/**
@brief Attaches an xor clause to the watchlists

The xor clause must be larger than 2, since a 2-long XOR clause is a varible
replacement instruction, really.
*/
void Solver::attachClause(XorClause& c)
{
    //assert(c.size() > 2);
    /*#ifdef DEBUG_ATTACH
    assert(assigns[c[0].var()] == l_Undef);
    assert(assigns[c[1].var()] == l_Undef);

    for (uint32_t i = 0; i < c.size(); i++) {
        assert(!subsumer || !subsumer->getVarElimed()[c[i].var()]);
        assert(!xorSubsumer->getVarElimed()[c[i].var()]);
    }
    #endif //DEBUG_ATTACH*/

    watches[Lit(c[0].var(), false).toInt()].push(clauseAllocator.getOffset((Clause*)&c));
    watches[Lit(c[0].var(), true).toInt()].push(clauseAllocator.getOffset((Clause*)&c));
    watches[Lit(c[1].var(), false).toInt()].push(clauseAllocator.getOffset((Clause*)&c));
    watches[Lit(c[1].var(), true).toInt()].push(clauseAllocator.getOffset((Clause*)&c));

    clauses_literals += c.size();
}

void Solver::attachBinClause(const Lit lit1, const Lit lit2, const bool learnt)
{
    /*#ifdef DEBUG_ATTACH
    assert(lit1.var() != lit2.var());
    assert(assigns[lit1.var()] == l_Undef);
    assert(value(lit2) == l_Undef || value(lit2) == l_False);

    assert(!subsumer || !subsumer->getVarElimed()[lit1.var()]);
    assert(!subsumer || !subsumer->getVarElimed()[lit2.var()]);

    assert(!xorSubsumer->getVarElimed()[lit1.var()]);
    assert(!xorSubsumer->getVarElimed()[lit2.var()]);
    #endif //DEBUG_ATTACH;*/

    watches[(~lit1).toInt()].push(Watched(lit2, learnt));
    watches[(~lit2).toInt()].push(Watched(lit1, learnt));

    #ifdef DUMP_STATS_FULL
    if (learnt) {
        watches[(~lit1).toInt()].last().glue = 2;
        watches[(~lit2).toInt()].last().glue = 2;
    } else {
        watches[(~lit1).toInt()].last().glue = -1;
        watches[(~lit2).toInt()].last().glue = -1;
    }
    #endif

    numBins++;
    if (learnt) learnts_literals += 2;
    else clauses_literals += 2;
}

/**
@brief Attach normal a clause to the watchlists

Handles 2, 3 and >3 clause sizes differently and specially
*/
void Solver::attachClause(Clause& c)
{
    //assert(c.size() > 2);
    /*#ifdef DEBUG_ATTACH
    assert(c[0].var() != c[1].var());
    assert(assigns[c[0].var()] == l_Undef);
    assert(value(c[1]) == l_Undef || value(c[1]) == l_False);

    for (uint32_t i = 0; i < c.size(); i++) {
        assert(!subsumer || !subsumer->getVarElimed()[c[i].var()]);
        assert(!xorSubsumer->getVarElimed()[c[i].var()]);
    }
    #endif //DEBUG_ATTACH*/

    if (c.size() == 3) {
        watches[(~c[0]).toInt()].push(Watched(c[1], c[2]));
        watches[(~c[1]).toInt()].push(Watched(c[0], c[2]));
        watches[(~c[2]).toInt()].push(Watched(c[0], c[1]));

        #ifdef DUMP_STATS_FULL
        if (c.learnt()) {
            watches[(~c[0]).toInt()].last().glue = 2;
            watches[(~c[1]).toInt()].last().glue = 2;
            watches[(~c[2]).toInt()].last().glue = 2;
        } else {
            watches[(~c[0]).toInt()].last().glue = -1;
            watches[(~c[1]).toInt()].last().glue = -1;
            watches[(~c[2]).toInt()].last().glue = -1;
        }
        #endif

    } else {
       // assert(c.size() > 2);
        ClauseOffset offset = clauseAllocator.getOffset(&c);
        watches[(~c[0]).toInt()].push(Watched(offset, c[2]));
        watches[(~c[1]).toInt()].push(Watched(offset, c[2]));
    }

    if (c.learnt())
        learnts_literals += c.size();
    else
        clauses_literals += c.size();
}

/**
@brief Calls detachModifiedClause to do the heavy-lifting
*/
void Solver::detachClause(const XorClause& c)
{
    detachModifiedClause(c[0].var(), c[1].var(), c.size(), &c);
}

/**
@brief Calls detachModifiedClause to do the heavy-lifting
*/
void Solver::detachClause(const Clause& c)
{
    detachModifiedClause(c[0], c[1], (c.size() == 3) ? c[2] : lit_Undef,  c.size(), &c);
}

/**
@brief Detaches a (potentially) modified clause

The first two literals might have chaned through modification, so they are
passed along as arguments -- they are needed to find the correct place where
the clause is
*/
void Solver::detachModifiedClause(const Lit lit1, const Lit lit2, const Lit lit3, const uint32_t origSize, const Clause* address)
{
    //assert(origSize > 2);

    ClauseOffset offset = clauseAllocator.getOffset(address);
    if (origSize == 3) {
        //The clause might have been longer, and has only recently
        //became 3-long. Check, and detach accordingly
        if (findWCl(watches[(~lit1).toInt()], offset)) goto fullClause;

        removeWTri(watches[(~lit1).toInt()], lit2, lit3);
        removeWTri(watches[(~lit2).toInt()], lit1, lit3);
        removeWTri(watches[(~lit3).toInt()], lit1, lit2);

    } else {
        fullClause:
        removeWCl(watches[(~lit1).toInt()], offset);
        removeWCl(watches[(~lit2).toInt()], offset);

    }

    if (address->learnt())
        learnts_literals -= origSize;
    else
        clauses_literals -= origSize;
}

/**
@brief Detaches a (potentially) modified xor clause

The first two vars might have chaned through modification, so they are passed
along as arguments.
*/
void Solver::detachModifiedClause(const Var var1, const Var var2, const uint32_t origSize, const XorClause* address)
{
    //assert(origSize > 2);

    ClauseOffset offset = clauseAllocator.getOffset(address);
    assert(findWXCl(watches[Lit(var1, false).toInt()], offset));
    assert(findWXCl(watches[Lit(var1, true).toInt()], offset));
    assert(findWXCl(watches[Lit(var2, false).toInt()], offset));
    assert(findWXCl(watches[Lit(var2, true).toInt()], offset));

    removeWXCl(watches[Lit(var1, false).toInt()], offset);
    removeWXCl(watches[Lit(var1, true).toInt()], offset);
    removeWXCl(watches[Lit(var2, false).toInt()], offset);
    removeWXCl(watches[Lit(var2, true).toInt()], offset);

    //assert(!address->learnt());
    clauses_literals -= origSize;
}

/**
@brief Revert to the state at given level

Also reverts all stuff in Gass-elimination
*/
void Solver::cancelUntil(int level)
{
    //#ifdef VERBOSE_DEBUG
    //cout << "Canceling until level " << level;
    //if (level > 0) cout << " sublevel: " << trail_lim[level];
    //cout << endl;
    //#endif

    if ((int)decisionLevel() > level) {
        //delete by alanwang
		/*
        #ifdef USE_GAUSS
        for (vector<Gaussian*>::iterator gauss = gauss_matrixes.begin(), end= gauss_matrixes.end(); gauss != end; gauss++)
            (*gauss)->canceling(trail_lim[level]);
        #endif //USE_GAUSS
        */
		 #ifdef USE_GAUSS
        for (vector<EnhanceGaussian*>::iterator gauss = EnhancGauss_matrixes.begin(), end= EnhancGauss_matrixes.end(); gauss != end; gauss++)
            (*gauss)->canceling(trail_lim[level]);
        #endif //USE_GAUSS 
		
        for (int sublevel = trail.size()-1; sublevel >= (int)trail_lim[level]; sublevel--) {
            Var var = trail[sublevel].var();
            //#ifdef VERBOSE_DEBUG
            //cout << "Canceling var " << var+1 << " sublevel: " << sublevel << endl;
            //#endif
            assigns[var] = l_Undef;
            //#ifdef ANIMATE3D
            //fprintf(stderr, "u %u\n", var);
            //#endif
            insertVarOrder(var);
            #ifdef ENABLE_UNWIND_GLUE
            if (unWindGlue[var] != NULL) {
                /*#ifdef UNWINDING_DEBUG
                std::cout << "unwind, var:" << var
                << " sublevel:" << sublevel
                << " coming from:" << (trail.size()-1)
                << " going until:" << (int)trail_lim[level]
                << std::endl;
                unWindGlue[var]->plainPrint();
                #endif //UNWINDING_DEBUG*/

                Clause*& clauseToFree = unWindGlue[var];
                detachClause(*clauseToFree);
                clauseAllocator.clauseFree(clauseToFree);
                clauseToFree = NULL;
            }
            #endif //ENABLE_UNWIND_GLUE
        }
        qhead = trail_lim[level];
        trail.shrink_(trail.size() - trail_lim[level]);
        trail_lim.shrink_(trail_lim.size() - level);
		
		if(clause_trail.size()>0&&conf.doPureliteral)
		{
			for (int sublevel = clause_trail.size()-1; sublevel >= (int)clause_trail_lim[level]; sublevel--)
			{
				uint32_t c_ind= clause_trail[sublevel]-2*nVars()-1;
				//printf("cind:%d \n", c_ind);
			   if(clauses_cpy[c_ind]!=NULL)
			    {
				//assert(c_ind==(clauses_cpy[c_ind])->get_cpyindex());
  				if( !(*clauses_cpy[c_ind]).getFreed()){
				  (*(clauses_cpy[c_ind])).set_issat(false);
				  //(*(clauses_cpy[c_ind])).set_satby(lit_Undef);
				  satby[c_ind]=lit_Undef.toInt();
				  }
				}
			
			
			}
		
		}
		
        
		if(conf.doPureliteral)
		{
			chead=clause_trail_lim[level];
			clause_trail.shrink_(clause_trail.size()-clause_trail_lim[level]);
			clause_trail_lim.shrink(clause_trail_lim.size()-level);
		}
    }

    //#ifdef VERBOSE_DEBUG
   // cout << "Canceling finished. (now at level: " << decisionLevel() << " sublevel: " << trail.size()-1 << ")" << endl;
    //#endif
}

void Solver::cancelUntilLight()
{
   // assert((int)decisionLevel() > 0);

    for (int sublevel = trail.size()-1; sublevel >= (int)trail_lim[0]; sublevel--) {
        Var var = trail[sublevel].var();
        assigns[var] = l_Undef;
    }
    qhead = trail_lim[0];
    trail.shrink_(trail.size() - trail_lim[0]);
    trail_lim.clear();
	
	if(clause_trail.size()>0&&conf.doPureliteral)
		{
			for (int sublevel = clause_trail.size()-1; sublevel >= (int)clause_trail_lim[0]; sublevel--)
			{
				uint32_t c_ind= clause_trail[sublevel]-2*nVars()-1;
			   if(clauses_cpy[c_ind]!=NULL)
			    {
				//assert(c_ind==(clauses_cpy[c_ind])->get_cpyindex());
  				if( !(*clauses_cpy[c_ind]).getFreed()){
				  (*(clauses_cpy[c_ind])).set_issat(false);
				  satby[c_ind]=lit_Undef.toInt();
				  }
				}
			
			
			}
		
		}
   
	if(conf.doPureliteral)
	{
	 chead= clause_trail_lim[0];
	 clause_trail.shrink_(clause_trail.size()-clause_trail_lim[0]);
	 clause_trail_lim.clear();
	}
}

/*const bool Solver::clearGaussMatrixes()
{
    assert(decisionLevel() == 0);
    #ifdef USE_GAUSS
    bool ret = gauss_matrixes.size() > 0;
    for (uint32_t i = 0; i < gauss_matrixes.size(); i++)
        delete gauss_matrixes[i];
    gauss_matrixes.clear();

    for (uint32_t i = 0; i != freeLater.size(); i++)
        clauseAllocator.clauseFree(freeLater[i]);
    freeLater.clear();

    return ret;
    #endif //USE_GAUSS
    return false;
}*/
/// add by hankf4

const bool Solver::clearEnGaussMatrixes()
{
    //assert(decisionLevel() == 0);
	
    #ifdef USE_GAUSS
	//std::cout << "clear matrixes:"<<EnhancGauss_matrixes.size()<< std::endl;
    bool ret = EnhancGauss_matrixes.size() > 0;
	
	if(gauss_learn_size < Gauss_learnts.size() ) {
		gauss_learn_size = Gauss_learnts.size() ;
	}
	
	
	//printf("DD Gauss_learnt_size: %d\n", Gauss_learnts.size());
	if(gaussconfig.add_clear){
		for (uint32_t i = 0; i < Gauss_learnts.size(); i++)
			removeClause(*Gauss_learnts[i]);
		Gauss_learnts.clear(); 
	}
   /*  if(restart_num >= 2){
		vector<bool> check;
		check.resize( Gauss_learnts.size() , false);
		int same = 0;
		int total_same = 0 ;
	
		for(Var i = 0 ; i < Gauss_learnts.size() ; i++){
			if(check[i] == true) continue;
			
			Clause* ii = Gauss_learnts[i];
			
			for(Var j= i+ 1 ; j < Gauss_learnts.size()  ; j++){
				Clause* jj = Gauss_learnts[j];
				same =0 ;
				for(Var a = 0 ; a < 3 ; a++){
					for(Var b =0 ; b < 3 ; b++){
						if((*ii)[a].var() == (*jj)[b].var() )
							same++;
					}
				}
				if(same == 3){
					total_same++;
					check[j] = true;
					
				 	for(Var a = 0 ; a < 3 ; a++){
						printf("%d ",(*ii)[a].var() ) ;
					}
					printf("==> ");
					for(Var a = 0 ; a < 3 ; a++){
						printf("%d ",(*jj)[a].var() ) ;
					}
					printf("\n"); 
				}
			}
		}
		
		printf("tatal_same:%d\n",total_same);
		
		total_same = 0;
		check.resize( Gauss_learnts.size() , false);
		int xor_three = 0;
		
		for(Var i = 0 ; i < xorclauses.size() ; i++){
			
			XorClause* ii = xorclauses[i];
			
			if(ii->size() == 3 ) xor_three++;
			
			if(ii->size() > 3)
				continue;
			
			for(Var j= 0 ; j < Gauss_learnts.size()  ; j++){
				if(check[j] == true) continue;
				
				Clause* jj = Gauss_learnts[j];
				same =0 ;
				for(Var a = 0 ; a < 3 ; a++){
					for(Var b =0 ; b < 3 ; b++){
						if((*ii)[a].var() == (*jj)[b].var() )
							same++;
					}
				}
				if(same == 3){
					total_same++;
					check[j] = true;
					
					for(Var a = 0 ; a < 3 ; a++){
						printf("%d ",(*ii)[a].var() ) ;
					}
					printf("==> ");
					for(Var a = 0 ; a < 3 ; a++){
						printf("%d ",(*jj)[a].var() ) ;
					}
					printf("\n");  
				} 
			}
		}
		
		printf("tatal_same:%d\n",total_same);
		printf("xor_three:%d\n",xor_three);
		
		
		exit(1);
	} */
/* 	if(conf.gauss_sta){
		for (vector<EnhanceGaussian*>::const_iterator gauss = EnhancGauss_matrixes.begin(), end= EnhancGauss_matrixes.end(); gauss != end; gauss++) {
			sum_Encalled += (*gauss)->enget_called();
			sum_Enpropagate += (*gauss)->enget_useful_prop();
			sum_Enconflict += (*gauss)->enget_useful_confl();
			sum_Enpropagate_two += (*gauss)->enget_useful_prop_two();
			sum_Enconflict_two += (*gauss)->enget_useful_confl_two();
			sum_Encalled_eliminate += (*gauss)->enget_eliminate_num();	
			
			sum_En_el_conflict_two += (*gauss)->enget_el_conflict_two();
			std::cout << "clear matrixes:"<<EnhancGauss_matrixes.size()<<"@@"<< (*gauss)->enget_el_conflict_two() <<  std::endl;
			
			sum_En_el_conflict += (*gauss)->enget_el_conflict();
			sum_En_el_propagate_two += (*gauss)->enget_el_propagate_two();
			sum_En_el_propagate += (*gauss)->enget_el_propagate();
			sum_already_true+=(*gauss)->enget_alreadytrue();
			sum_el_already_true+=(*gauss)->enget_el_enget_alreadytrue();
			sum_already_true_stop+=(*gauss)->enget_already_true_stop();
		} 
	} */
	//assert(EnhancGauss_matrixes_size == EnhancGauss_matrixes.size());
    for (uint32_t i = 0; i < EnhancGauss_matrixes_size; i++)  // delete matrix
        delete EnhancGauss_matrixes[i];
    EnhancGauss_matrixes.clear();
	EnhancGauss_matrixes_size = 0;
//	for(size_t ii = 0 ; ii < GausWatches.size() ; ii++){   //  delete gauss watch list
//		GausWatches[ii].clear();
//	}
	

    return ret;
    #endif //USE_GAUSS
	
    return false;
}





///------------
/**
@brief Returns what polarity[] should be set as default based on polarity_mode

since polarity is filled with Lit::sign() , "true" here means an inverted
signed-ness, i.e. a FALSE default value. And vice-versa
*/
inline bool Solver::defaultPolarity()
{
    switch(conf.polarity_mode) {
        case polarity_false:
            return true;
        case polarity_true:
            return false;
        case polarity_rnd:
            return mtrand.randInt(1);
        case polarity_auto:
            return true;
        default:
            assert(false);
    }

    return true;
}

/**
@brief Tally votes for a default TRUE or FALSE value for the variable using the Jeroslow-Wang method

@p votes[inout] Votes are tallied at this place for each variable
@p cs The clause to tally votes for
*/
void Solver::tallyVotes(const vec<Clause*>& cs, vec<double>& votes) const
{
    for (const Clause * const*it = cs.getData(), * const*end = it + cs.size(); it != end; it++) {
        const Clause& c = **it;
        if (c.learnt()) continue;

        double divider;
        if (c.size() > 63) divider = 0.0;
        else divider = 1.0/(double)((uint64_t)1<<(c.size()-1));

        for (const Lit *it2 = c.getData(), *end2 = c.getDataEnd(); it2 != end2; it2++) {
            if (it2->sign()) votes[it2->var()] += divider;
            else votes[it2->var()] -= divider;
        }
    }
}

void Solver::tallyVotesBin(vec<double>& votes) const
{
    uint32_t wsLit = 0;
    for (const vec<Watched> *it = watches.getData(), *end = watches.getDataEnd(); it != end; it++, wsLit++) {
        Lit lit = ~Lit::toLit(wsLit);
        const vec<Watched>& ws = *it;
        for (vec<Watched>::const_iterator it2 = ws.getData(), end2 = ws.getDataEnd(); it2 != end2; it2++) {
            if (it2->isBinary() && lit.toInt() < it2->getOtherLit().toInt()) {
                if (!it2->getLearnt()) {
                    if (lit.sign()) votes[lit.var()] += 0.5;
                    else votes[lit.var()] -= 0.5;

                    Lit lit2 = it2->getOtherLit();
                    if (lit2.sign()) votes[lit2.var()] += 0.5;
                    else votes[lit2.var()] -= 0.5;
                }
            }
        }
    }
}

/**
@brief Tally votes a default TRUE or FALSE value for the variable using the Jeroslow-Wang method

For XOR clause, we simply add some weight for a FALSE default, i.e. being in
xor clauses makes the variabe more likely to be FALSE by default
*/
void Solver::tallyVotes(const vec<XorClause*>& cs, vec<double>& votes) const
{
    for (const XorClause * const*it = cs.getData(), * const*end = it + cs.size(); it != end; it++) {
        const XorClause& c = **it;
        double divider;
        if (c.size() > 63) divider = 0.0;
        else divider = 1.0/(double)((uint64_t)1<<(c.size()-1));

        for (const Lit *it2 = c.getData(), *end2 = c.getDataEnd(); it2 != end2; it2++) {
            votes[it2->var()] += divider;
        }
    }
}

/**
@brief Tallies votes for a TRUE/FALSE default polarity using Jeroslow-Wang

Voting is only used if polarity_mode is "polarity_auto". This is the default.
Uses the tallyVotes() functions to tally the votes
*/
void Solver::calculateDefaultPolarities()
{
    //#ifdef VERBOSE_DEBUG_POLARITIES
    //std::cout << "Default polarities: " << std::endl;
    //#endif

    //assert(decisionLevel() == 0);
    if (conf.polarity_mode == polarity_auto) {
        double myTime = cpuTime();

        vec<double> votes(nVars(), 0.0);

        tallyVotes(clauses, votes);
        tallyVotesBin(votes);
        tallyVotes(xorclauses, votes);

        Var i = 0;
        uint32_t posPolars = 0;
        uint32_t undecidedPolars = 0;
        for (const double *it = votes.getData(), *end = votes.getDataEnd(); it != end; it++, i++) {
            polarity[i] = (*it >= 0.0);
            posPolars += (*it < 0.0);
            undecidedPolars += (*it == 0.0);
            #ifdef VERBOSE_DEBUG_POLARITIES
            std::cout << !defaultPolarities[i] << ", ";
            #endif //VERBOSE_DEBUG_POLARITIES
        }

        if (conf.verbosity >= 2) {
            std::cout << "c Calc default polars - "
            << " time: " << std::fixed << std::setw(6) << std::setprecision(2) << (cpuTime() - myTime) << " s"
            << " pos: " << std::setw(7) << posPolars
            << " undec: " << std::setw(7) << undecidedPolars
            << " neg: " << std::setw(7) << nVars()-  undecidedPolars - posPolars
            << std:: endl;
        }
    } else {
        for (uint32_t i = 0; i < polarity.size(); i++) {
            polarity[i] = defaultPolarity();
        }
    }

    //#ifdef VERBOSE_DEBUG_POLARITIES
    //std::cout << std::endl;
    //#endif //VERBOSE_DEBUG_POLARITIES
}

void Solver::calcReachability()
{
    double myTime = cpuTime();

    for (uint32_t i = 0; i < nVars()*2; i++) {
        litReachable[i] = LitReachData();
    }

    for (uint32_t i = 0; i < order_heap.size(); i++) for (uint32_t sig1 = 0; sig1 < 2; sig1++)  {
        Lit lit = Lit(order_heap[i], sig1);
        if (value(lit.var()) != l_Undef
            || (subsumer && subsumer->getVarElimed()[lit.var()])
            || xorSubsumer->getVarElimed()[lit.var()]
            || !decision_var[lit.var()])
            continue;

        vector<Lit>& cache = transOTFCache[(~lit).toInt()].lits;
        uint32_t cacheSize = cache.size();
        for (vector<Lit>::const_iterator it = cache.begin(), end = cache.end(); it != end; it++) {
            /*if (solver.value(it->var()) != l_Undef
            || solver.subsumer->getVarElimed()[it->var()]
            || solver.xorSubsumer->getVarElimed()[it->var()])
            continue;*/
            if ((*it == lit) || (*it == ~lit)) continue;
            if (litReachable[it->toInt()].lit == lit_Undef || litReachable[it->toInt()].numInCache < cacheSize) {
                litReachable[it->toInt()].lit = lit;
                litReachable[it->toInt()].numInCache = cacheSize;
            }
        }
    }

    /*for (uint32_t i = 0; i < nVars()*2; i++) {
        std::sort(litReachable[i].begin(), litReachable[i].end(), MySorterX(transOTFCache));
    }*/

    /*for (uint32_t i = 0; i < nVars()*2; i++) {
        vector<Lit>& myset = litReachable[i];
        for (uint32_t i2 = 0; i2 < myset.size(); i2++) {
            std::cout << transOTFCache[myset[i2].toInt()].lits.size() << " , ";
        }
        std::cout << std::endl;
    }*/

    if (conf.verbosity >= 1) {
        std::cout << "c calculated reachability. Time: " << (cpuTime() - myTime) << std::endl;
    }
}

void Solver::saveOTFData()
{
    //assert(decisionLevel() == 1);

    Lit lev0Lit = trail[trail_lim[0]];
    Solver::TransCache& oTFCache = transOTFCache[(~lev0Lit).toInt()];
    oTFCache.conflictLastUpdated = conflicts;
    oTFCache.lits.clear();

    for (int sublevel = trail.size()-1; sublevel > (int)trail_lim[0]; sublevel--) {
        Lit lit = trail[sublevel];
        oTFCache.lits.push_back(lit);
    }
}

//**********************************
// Major methods:
//**********************************

/**
@brief Picks a branching variable and its value (True/False)

We do three things here:
-# Try to do random decision (rare, less than 2%)
-# Try acitivity-based decision

Then, we pick a sign (True/False):
\li If we are in search-burst mode ("simplifying" is set), we pick a sign
totally randomly
\li Otherwise, we simply take the saved polarity
*/
Lit Solver::pickBranchLit()
{
    //#ifdef VERBOSE_DEBUG
    //cout << "decision level: " << decisionLevel() << " ";
    //#endif

    Var next = var_Undef;

    /* Skip variables which have already been defined (this will usually happen
     * because of propagations/implicit assignments) */
    for (unsigned int i = decisionLevel(); i < branching_variables.size(); ++i) {
        Var v = branching_variables[i];
        if (v < nVars()
            && (subsumer && !subsumer->getVarElimed()[v])
            && !xorSubsumer->getVarElimed()[v]
            && assigns[v] == l_Undef
        ) {
            next = v;
            break;
        }
    }

    bool random = mtrand.randDblExc() < conf.random_var_freq;

    // Random decision:
    if (next == var_Undef && random && !order_heap.empty()) {
        if (conf.restrictPickBranch == 0)
            next = order_heap[mtrand.randInt(order_heap.size()-1)];
        else
            next = order_heap[mtrand.randInt(std::min((uint32_t)order_heap.size()-1, conf.restrictPickBranch))];

        if (assigns[next] == l_Undef && decision_var[next])
            rnd_decisions++;
    }

    bool signSet = false;
    bool signSetTo = false;
    // Activity based decision:
    while (next == var_Undef
      || assigns[next] != l_Undef
      || !decision_var[next]) {
        if (order_heap.empty()) {
            next = var_Undef;
            break;
        }

        next = order_heap.removeMin();
        if (!simplifying && value(next) == l_Undef && decision_var[next]) {
            signSet = true;
            if (avgBranchDepth.isvalid())
                signSetTo = polarity[next] ^ (mtrand.randInt(avgBranchDepth.getAvgUInt() * ((lastSelectedRestartType == static_restart) ? 2 : 1) ) == 1);
            else
                signSetTo = polarity[next];
            Lit nextLit = Lit(next, signSetTo);
            Lit lit2 = litReachable[nextLit.toInt()].lit;
            if (lit2 != lit_Undef && value(lit2.var()) == l_Undef && decision_var[lit2.var()] && mtrand.randInt(1) == 1) {
                insertVarOrder(next);
                next = litReachable[nextLit.toInt()].lit.var();
                signSetTo = litReachable[nextLit.toInt()].lit.sign();
            }
        }
    }

    //if "simplifying" is set, i.e. if we are in a burst-search mode, then
    //randomly pick a sign. Otherwise, if RANDOM_LOOKAROUND_SEARCHSPACE is
    //defined, we check the default polarity, and we may change it a bit
    //randomly based on the average branch depth. Otherwise, we just go for the
    //polarity that has been saved
    bool sign;
    if (next != var_Undef)  {
        if (signSet) {
            sign = signSetTo;
        } else {
            if (simplifying && random)
                sign = mtrand.randInt(1);
            else if (avgBranchDepth.isvalid())
                sign = polarity[next] ^ (mtrand.randInt(avgBranchDepth.getAvgUInt() * ((lastSelectedRestartType == static_restart) ? 2 : 1) ) == 1);
            else
                sign = polarity[next];
        }
    }

   // assert(next == var_Undef || value(next) == l_Undef);

    if (next == var_Undef) {
       // #ifdef VERBOSE_DEBUG
       // cout << "SAT!" << endl;
       // #endif
        return lit_Undef;
    } else {
        Lit lit(next,sign);
       /* #ifdef VERBOSE_DEBUG
        assert(decision_var[lit.var()]);
        cout << "decided on: " << lit.var()+1 << " to set:" << !lit.sign() << endl;
        #endif*/
        return lit;
    }
}

/**
@brief Checks subsumption. Used in on-the-fly subsumption code

Assumes 'seen' is cleared (will leave it cleared)
*/
template<class T1, class T2>
bool subset(const T1& A, const T2& B, vector<char>& seen)
{
    for (uint32_t i = 0; i != B.size(); i++)
        seen[B[i].toInt()] = 1;
    for (uint32_t i = 0; i != A.size(); i++) {
        if (!seen[A[i].toInt()]) {
            for (uint32_t i = 0; i != B.size(); i++)
                seen[B[i].toInt()] = 0;
            return false;
        }
    }
    for (uint32_t i = 0; i != B.size(); i++)
        seen[B[i].toInt()] = 0;
    return true;
}


/**
@brief    Analyze conflict and produce a reason clause.

Pre-conditions:
\li  'out_learnt' is assumed to be cleared.
\li Current decision level must be greater than root level.

Post-conditions:
\li 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.

Effect: Will undo part of the trail, upto but not beyond the assumption of the
current decision level.

@return NULL if the conflict doesn't on-the-fly subsume the last clause, and
the pointer of the clause if it does
*/
Clause* Solver::analyze(PropBy conflHalf, vec<Lit>& out_learnt, int& out_btlevel, uint32_t &glue, const bool update)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;
    out_btlevel = 0;

    PropByFull confl(conflHalf, failBinLit, clauseAllocator);
    PropByFull oldConfl;

    do {
        //assert(!confl.isNULL());          // (otherwise should be UIP)

        if (update && restartType == static_restart && confl.isClause() && confl.getClause()->learnt())
            claBumpActivity(*confl.getClause());

        for (uint32_t j = (p == lit_Undef) ? 0 : 1, size = confl.size(); j != size; j++) {
            Lit q = confl[j];
            const Var my_var = q.var();

            if (!seen[my_var] && level[my_var] > 0) {
                varBumpActivity(my_var);
                seen[my_var] = 1;
                //assert(level[my_var] <= (int)decisionLevel());
                if (level[my_var] >= (int)decisionLevel()) {
                    pathC++;
                    if (lastSelectedRestartType == dynamic_restart
                        && reason[q.var()].isClause()
                        && !reason[q.var()].isNULL()
                        && clauseAllocator.getPointer(reason[q.var()].getClause())->learnt())
                        lastDecisionLevel.push(q.var());
                } else {
                    out_learnt.push(q);
                    if (level[my_var] > out_btlevel)
                        out_btlevel = level[my_var];
                }
            }
        }

        // Select next clause to look at:
        while (!seen[trail[index--].var()]);
        p     = trail[index+1];
        oldConfl = confl;
        confl = PropByFull(reason[p.var()], failBinLit, clauseAllocator);
        if (confl.isClause()) __builtin_prefetch(confl.getClause());
        seen[p.var()] = 0;
        pathC--;

    } while (pathC > 0);
   // assert(pathC == 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    uint32_t i, j;
    if (conf.expensive_ccmin) {
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(out_learnt[i].var()); // (maintain an abstraction of levels involved in conflict)

        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason[out_learnt[i].var()].isNULL() || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
    } else {
        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++) {
            PropByFull c(reason[out_learnt[i].var()], failBinLit, clauseAllocator);

            for (uint32_t k = 1, size = c.size(); k < size; k++) {
                if (!seen[c[k].var()] && level[c[k].var()] > 0) {
                    out_learnt[j++] = out_learnt[i];
                    break;
                }
            }
        }
    }
    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    for (uint32_t j = 0; j != analyze_toclear.size(); j++)
        seen[analyze_toclear[j].var()] = 0;    // ('seen[]' is now cleared)

    if (conf.doMinimLearntMore && out_learnt.size() > 1)
        minimiseLeartFurther(out_learnt, calcNBLevels(out_learnt));

    glue = calcNBLevels(out_learnt);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else {
        uint32_t max_i = 1;
        for (uint32_t i = 2; i < out_learnt.size(); i++)
            if (level[out_learnt[i].var()] > level[out_learnt[max_i].var()])
                max_i = i;
        std::swap(out_learnt[max_i], out_learnt[1]);
        out_btlevel = level[out_learnt[1].var()];
    }

    if (lastSelectedRestartType == dynamic_restart) {
        #ifdef UPDATE_VAR_ACTIVITY_BASED_ON_GLUE
        for(uint32_t i = 0; i != lastDecisionLevel.size(); i++) {
            PropBy cl = reason[lastDecisionLevel[i]];
            if (cl.isClause() && clauseAllocator.getPointer(cl.getClause())->getGlue() < glue)
                varBumpActivity(lastDecisionLevel[i]);
        }
        lastDecisionLevel.clear();
        #endif
    }

    //We can only on-the-fly subsume clauses that are not 2- or 3-long
    //furthermore, we cannot subsume a clause that is marked for deletion
    //due to its high glue value
    if (!conf.doOTFSubsume
        || out_learnt.size() == 1
        || !oldConfl.isClause()
        || oldConfl.getClause()->isXor()
        #ifdef ENABLE_UNWIND_GLUE
        || (conf.doMaxGlueDel && oldConfl.getClause()->getGlue() > conf.maxGlue)
        #endif //ENABLE_UNWIND_GLUE
        || out_learnt.size() >= oldConfl.getClause()->size()) return NULL;

    if (!subset(out_learnt, *oldConfl.getClause(), seen)) return NULL;

    improvedClauseNo++;
    improvedClauseSize += oldConfl.getClause()->size() - out_learnt.size();
    return oldConfl.getClause();
}

/**
@brief Performs on-the-fly self-subsuming resolution

Only uses binary and tertiary clauses already in the watchlists in native
form to carry out the forward-self-subsuming resolution
*/
void Solver::minimiseLeartFurther(vec<Lit>& cl, const uint32_t glue)
{
    //80 million is kind of a hack. It seems that the longer the solving
    //the slower this operation gets. So, limiting the "time" with total
    //number of conflict literals is maybe a good way of doing this
    bool clDoMinLRec = false;
    if (conf.doCacheOTFSSR && conf.doMinimLMoreRecur) {
        switch(lastSelectedRestartType) {
            case dynamic_restart :
                clDoMinLRec |= glue < 0.6*glueHistory.getAvgAllDouble();
                //NOTE: No "break;" here on purpose
            case static_restart :
                clDoMinLRec |= cl.size() < 0.6*conflSizeHist.getAvgDouble();
                break;
            default :
                assert(false);
        }
    }

    if (clDoMinLRec) moreRecurMinLDo++;
    uint64_t thisUpdateTransOTFSSCache = UPDATE_TRANSOTFSSR_CACHE;
    if (tot_literals > 80000000) thisUpdateTransOTFSSCache *= 2;

    //To count the "amount of time" invested in doing transitive on-the-fly
    //self-subsuming resolution
    uint32_t moreRecurProp = 0;

    for (uint32_t i = 0; i < cl.size(); i++) seen[cl[i].toInt()] = 1;
    for (Lit *l = cl.getData(), *end = cl.getDataEnd(); l != end; l++) {
        if (seen[l->toInt()] == 0) continue;
        Lit lit = *l;

        if (clDoMinLRec) {
            if (moreRecurProp > 450
                ||  (transOTFCache[l->toInt()].conflictLastUpdated != std::numeric_limits<uint64_t>::max()
                    && (transOTFCache[l->toInt()].conflictLastUpdated + thisUpdateTransOTFSSCache >= conflicts))
            ) {
                for (vector<Lit>::const_iterator it = transOTFCache[l->toInt()].lits.begin(), end2 = transOTFCache[l->toInt()].lits.end(); it != end2; it++) {
                    seen[(~(*it)).toInt()] = 0;
                }
            } else {
                updateTransCache++;
                transMinimAndUpdateCache(lit, moreRecurProp);
            }
        }

        //watched is messed: lit is in watched[~lit]
        vec<Watched>& ws = watches[(~lit).toInt()];
        for (vec<Watched>::iterator i = ws.getData(), end = ws.getDataEnd(); i != end; i++) {
            if (i->isBinary()) {
                seen[(~i->getOtherLit()).toInt()] = 0;
                continue;
            }

            if (i->isTriClause()) {
                if (seen[(~i->getOtherLit()).toInt()] && seen[i->getOtherLit2().toInt()]) {
                    seen[(~i->getOtherLit()).toInt()] = 0;
                }
                if (seen[(~i->getOtherLit2()).toInt()] && seen[i->getOtherLit().toInt()]) {
                    seen[(~i->getOtherLit2()).toInt()] = 0;
                }
                continue;
            }

            //watches are mostly sorted, so it's more-or-less OK to break
            //  if non-bi or non-tri is encountered
            break;
        }
    }

    uint32_t removedLits = 0;
    Lit *i = cl.getData();
    Lit *j= i;
    //never remove the 0th literal
    seen[cl[0].toInt()] = 1;
    for (Lit* end = cl.getDataEnd(); i != end; i++) {
        if (seen[i->toInt()]) *j++ = *i;
        else removedLits++;
        seen[i->toInt()] = 0;
    }
    numShrinkedClause += (removedLits > 0);
    numShrinkedClauseLits += removedLits;
    cl.shrink_(i-j);

    #ifdef VERBOSE_DEBUG
    std::cout << "c Removed further " << removedLits << " lits" << std::endl;
    #endif
}

void Solver::transMinimAndUpdateCache(const Lit lit, uint32_t& moreRecurProp)
{
    vector<Lit>& allAddedToSeen2 = transOTFCache[lit.toInt()].lits;
    allAddedToSeen2.clear();

    toRecursiveProp.push(lit);
    while(!toRecursiveProp.empty()) {
        Lit thisLit = toRecursiveProp.top();
        toRecursiveProp.pop();
        //watched is messed: lit is in watched[~lit]
        vec<Watched>& ws = watches[(~thisLit).toInt()];
        moreRecurProp += ws.size() +10;
        for (vec<Watched>::iterator i = ws.getData(), end = ws.getDataEnd(); i != end; i++) {
            if (i->isBinary()) {
                moreRecurProp += 5;
                Lit otherLit = i->getOtherLit();
                //don't do indefinite recursion, and don't remove "a" when doing self-subsuming-resolution with 'a OR b'
                if (seen2[otherLit.toInt()] != 0 || otherLit == ~lit) break;
                seen2[otherLit.toInt()] = 1;
                allAddedToSeen2.push_back(otherLit);
                toRecursiveProp.push(~otherLit);
            } else {
                break;
            }
        }
    }
    //assert(toRecursiveProp.empty());

    for (vector<Lit>::const_iterator it = allAddedToSeen2.begin(), end = allAddedToSeen2.end(); it != end; it++) {
        seen[(~(*it)).toInt()] = 0;
        seen2[it->toInt()] = 0;
    }

    transOTFCache[lit.toInt()].conflictLastUpdated = conflicts;
}

/**
@brief Check if 'p' can be removed from a learnt clause

'abstract_levels' is used to abort early if the algorithm is
visiting literals at levels that cannot be removed later.
*/
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear();
    analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0) {
        ///assert(!reason[analyze_stack.last().var()].isNULL());
        PropByFull c(reason[analyze_stack.last().var()], failBinLit, clauseAllocator);

        analyze_stack.pop();

        for (uint32_t i = 1, size = c.size(); i < size; i++) {
            Lit p  = c[i];
            if (!seen[p.var()] && level[p.var()] > 0) {
                if (!reason[p.var()].isNULL() && (abstractLevel(p.var()) & abstract_levels) != 0) {
                    seen[p.var()] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                } else {
                    for (uint32_t j = top; j != analyze_toclear.size(); j++)
                        seen[analyze_toclear[j].var()] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[p.var()] = 1;

    for (int32_t i = (int32_t)trail.size()-1; i >= (int32_t)trail_lim[0]; i--) {
        Var x = trail[i].var();
        if (seen[x]) {
            if (reason[x].isNULL()) {
                //assert(level[x] > 0);
                out_conflict.push(~trail[i]);
            } else {
                PropByFull c(reason[x], failBinLit, clauseAllocator);
                for (uint32_t j = 1, size = c.size(); j < size; j++)
                    if (level[c[j].var()] > 0)
                        seen[c[j].var()] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[p.var()] = 0;
}

/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
/**
@brief Propagates a binary clause

Need to be somewhat tricky if the clause indicates that current assignement
is incorrect (i.e. both literals evaluate to FALSE). If conflict if found,
sets failBinLit
*/
template<bool full>
inline bool Solver::propBinaryClause(vec<Watched>::iterator &i, const Lit p, PropBy& confl)
{
    lbool val = value(i->getOtherLit());
    if (val.isUndef()) {
        if (full) uncheckedEnqueue(i->getOtherLit(), PropBy(p));
        else      uncheckedEnqueueLight(i->getOtherLit());
       /* #ifdef DUMP_STATS_FULL
        assert(((i->glue > 0) == i->getLearnt()));
        if (full && i->glue > 0 && !simplifying) {
            std::cout << "Prop by learnt size: " << 2 << std::endl;
            std::cout << "Prop by learnt glue: " << i->glue << std::endl;
        }
        #endif //DUMP_STATS_FULL
		*/
    } else if (val == l_False) {
        confl = PropBy(p);
        failBinLit = i->getOtherLit();
        qhead = trail.size();
		chead=  clause_trail.size();/// add by alanwang
        /*#ifdef DUMP_STATS_FULL
        assert(((i->glue > 0) == i->getLearnt()));
        if (full && i->glue > 0 && !simplifying) {
            std::cout << "Confl by learnt size: " << 2 << std::endl;
            std::cout << "Confl by learnt glue: " << i->glue << std::endl;
        }
        #endif //DUMP_STATS_FULL*/

        return false;
    }

    return true;
}

/**
@brief Propagates a tertiary (3-long) clause

Need to be somewhat tricky if the clause indicates that current assignement
is incorrect (i.e. all 3 literals evaluate to FALSE). If conflict is found,
sets failBinLit
*/
template<bool full>
inline bool Solver::propTriClause(vec<Watched>::iterator &i, const Lit p, PropBy& confl)
{
    lbool val = value(i->getOtherLit());
    if (val == l_True) return true;

    lbool val2 = value(i->getOtherLit2());
    if (val.isUndef() && val2 == l_False) {
        if (full) uncheckedEnqueue(i->getOtherLit(), PropBy(p, i->getOtherLit2()));
        else      uncheckedEnqueueLight(i->getOtherLit());
       /* #ifdef DUMP_STATS_FULL
        assert(conf.isPlain);
        if (full && i->glue > 0 && !simplifying) {
            std::cout << "Prop by learnt size: " << 3 << std::endl;
            std::cout << "Prop by learnt glue: " << i->glue << std::endl;
        }
        #endif //DUMP_STATS_FULL*/
    } else if (val == l_False && val2.isUndef()) {
        if (full) uncheckedEnqueue(i->getOtherLit2(), PropBy(p, i->getOtherLit()));
        else      uncheckedEnqueueLight(i->getOtherLit2());
        /*#ifdef DUMP_STATS_FULL
        assert(conf.isPlain);
        if (full && i->glue > 0 && !simplifying) {
            std::cout << "Prop by learnt size: " << 3 << std::endl;
            std::cout << "Prop by learnt glue: " << i->glue << std::endl;
        }
        #endif //DUMP_STATS_FULL*/
    } else if (val == l_False && val2 == l_False) {
        confl = PropBy(p, i->getOtherLit2());
        failBinLit = i->getOtherLit();
        qhead = trail.size();
        /*#ifdef DUMP_STATS_FULL
        assert(conf.isPlain);
        if (full && i->glue > 0 && !simplifying) {
            std::cout << "Confl by learnt size: " << 3 << std::endl;
            std::cout << "Confl by learnt glue: " << i->glue << std::endl;
        }
        #endif //DUMP_STATS_FULL*/

        return false;
    }

    return true;
}

/**
@brief Propagates a tertiary (3-long) clause

We have blocked literals in this case in the watchlist. That must be checked
and updated.
*/
template<bool full>
inline bool Solver::propNormalClause(vec<Watched>::iterator &i, vec<Watched>::iterator &j, const Lit p, PropBy& confl, const bool update)
{
    if (value(i->getBlockedLit()).getBool()) {
        // Clause is sat
        *j++ = *i;
        return true;
    }
    const uint32_t offset = i->getNormOffset();
    Clause& c = *clauseAllocator.getPointer(offset);

    // Make sure the false literal is data[1]:
    if (c[0] == ~p) {
        std::swap(c[0], c[1]);
    }

    //assert(c[1] == ~p);

    // If 0th watch is true, then clause is already satisfied.
    if (value(c[0]).getBool()) {
        *j = Watched(offset, c[0]);
        j++;
        return true;
    }
    // Look for new watch:
    for (Lit *k = c.getData() + 2, *end2 = c.getDataEnd(); k != end2; k++) {
        if (value(*k) != l_False) {
            c[1] = *k;
            *k = ~p;
            watches[(~c[1]).toInt()].push(Watched(offset, c[0]));
            return true;
        }
    }

    // Did not find watch -- clause is unit under assignment:
    *j++ = *i;
    if (value(c[0]) == l_False) {
        //#ifdef DUMP_STATS_FULL
        /*if (full && c.learnt() && !simplifying) {
            std::cout << "Confl by learnt size: " << c.size() << std::endl;
            std::cout << "Confl by learnt glue: " << c.getGlue() << std::endl;
            assert(!conf.isPlain || c.getGlue() > 1);
        }
        #endif //DUMP_STATS_FULL*/
        confl = PropBy(offset);
        qhead = trail.size();
        return false;
    } else {
        /*#ifdef DUMP_STATS_FULL
        if (full && c.learnt() && !simplifying) {
            std::cout << "Prop by learnt size: " << c.size() << std::endl;
            std::cout << "Prop by learnt glue: " << c.getGlue() << std::endl;
            assert(!conf.isPlain || c.getGlue() > 1);
        }
        #endif //DUMP_STATS_FULL*/

        if (full) uncheckedEnqueue(c[0], offset);
        else      uncheckedEnqueueLight(c[0]);
        #ifdef DYNAMICALLY_UPDATE_GLUE
        if (update && full && c.learnt() && c.getGlue() > 2) {
            uint32_t glue = calcNBLevels(c);
            if (glue+1 < c.getGlue()) {
                //c.setGlue(std::min(nbLevels, MAX_THEORETICAL_GLUE);
                c.setGlue(glue);
            }
        }
        #endif
    }

    return true;
}

/**
@brief Propagates a tertiary (3-long) clause

Strangely enough, we need to have 4 literals in the wathclists:
for the first two varialbles, BOTH negations (v and ~v). This means quite some
pain, since we need to remove v when moving ~v and vica-versa. However, it means
better memory-accesses since the watchlist is already in the memory...

\todo maybe not worth it, and a variable-based watchlist should be used
*/
template<bool full>
inline bool Solver::propXorClause(vec<Watched>::iterator &i, vec<Watched>::iterator &j, const Lit p, PropBy& confl)
{
    ClauseOffset offset = i->getXorOffset();
    XorClause& c = *(XorClause*)clauseAllocator.getPointer(offset);

    // Make sure the false literal is data[1]:
    if (c[0].var() == p.var()) {
        Lit tmp(c[0]);
        c[0] = c[1];
        c[1] = tmp;
    }
    //assert(c[1].var() == p.var());

    bool final = c.xorEqualFalse();
    for (uint32_t k = 0, size = c.size(); k != size; k++ ) {
        const lbool& val = assigns[c[k].var()];
        if (val.isUndef() && k >= 2) {
            Lit tmp(c[1]);
            c[1] = c[k];
            c[k] = tmp;
            removeWXCl(watches[(~p).toInt()], offset);
            watches[Lit(c[1].var(), false).toInt()].push(offset);
            watches[Lit(c[1].var(), true).toInt()].push(offset);
            return true;
        }

        c[k] = c[k].unsign() ^ val.getBool();
        final ^= val.getBool();
    }

    // Did not find watch -- clause is unit under assignment:
    *j++ = *i;

    if (assigns[c[0].var()].isUndef()) {
        c[0] = c[0].unsign()^final;
        if (full) uncheckedEnqueue(c[0], offset);
        else      uncheckedEnqueueLight(c[0]);
    } else if (!final) {
        confl = PropBy(offset);
        qhead = trail.size();
        return false;
    } else {
        Lit tmp(c[0]);
        c[0] = c[1];
        c[1] = tmp;
    }

    return true;
}


/// add by hankf4
/**
@brief Does the Gause eliminateion

Add by hankf4
*/

inline void Solver::Gauss_elimination(const Lit p, PropBy& confl)
{
 	//printf("DD : %d\n",p.var());
	bool do_eliminate = false;
	Var e_var;
	uint16_t e_row_n ;
	uint16_t matrix_id = 0;
	
	vec<GausWatched>&  ws  = GausWatches[p.var()];
	vec<GausWatched>::iterator i = ws.getData();
	vec<GausWatched>::iterator j = i;

	vec<GausWatched>::iterator end = ws.getDataEnd();
	
	if(i != end)
		matrix_id = (*i).matrix_num;
	else
		return ;
	
		
	
	for (; i != end; i++) {
		//assert(matrix_id == (*i).matrix_num);
		if(EnhancGauss_matrixes[matrix_id]->find_truths( i ,j , p.var()  , confl ,(*i).row_id ,do_eliminate , e_var , e_row_n ))
			continue;
		else{
			conflic_ingauss = true;
			break;
		}
	}
	
	if (i != end) {  // must conflict
		//debug_size2 = ws.size();
		i++;
		//copy remaining watches
		vec<GausWatched>::iterator j2 = i;
		vec<GausWatched>::iterator i2 = j;
		
		for(i2 = i, j2 = j; i2 != end; i2++) {	
			*j2 = *i2;
			//assert(solver.nVars() > *j2 );
			//assert(*j2 < m.)
			//cur_matrixset.nbAdrress[*j2] = j2; // update nbasic watch list; 
			j2++;
		}
	
		//memmove(j, i, sizeof(Watched)*(end-i));
	}
	//assert(i >= j);
	ws.shrink_(i-j);
	
	if(do_eliminate){
		//PackedMatrix::iterator rowIt = cur_matrixset.matrix.beginMatrix() + e_row_n;
		EnhancGauss_matrixes[matrix_id]->eliminate_col(e_var , e_row_n , p.var() ,confl);
		
	}	
	
  	for (vector<EnhanceGaussian*>::iterator gauss = EnhancGauss_matrixes.begin(), end = EnhancGauss_matrixes.end(); gauss != end; gauss++) {
        (*gauss)->Debug_funtion();
    }   
	
}


///------------------


/**
@brief Does the propagation

Basically, it goes through the watchlists recursively, and calls the appropirate
propagaton function
*/
template<bool full>
PropBy Solver::propagate(const bool update)
{
    PropBy confl;
    uint32_t num_props = 0;

   // #ifdef VERBOSE_DEBUG
    //cout << "Propagation started" << endl;
   // #endif

    while (qhead < trail.size()) {
        Lit p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
		
		
		if(conf.doPureliteral&&chead<clause_trail.size()&&constructpure){
			while(chead<clause_trail.size())
			{
			 // if(conf.doPureliteral&&dopurenow&&constructpure){
			  uint32_t clause_ind=clause_trail[chead++]-2*nVars()-1;
			  //double   cpu_time2 = cpuTime();
			  trytofindpurelit(clause_ind);
			  //printf("try to find\n");
			  //dopuretime+= cpuTime()- cpu_time2;
			  
			 
			}
		}
		
		
        vec<Watched>&  ws  = watches[p.toInt()];
        num_props += (ws.size()/2) + 2;

        //#ifdef VERBOSE_DEBUG
        //cout << "Propagating lit " << p << endl;
        //cout << "ws origSize: "<< ws.size() << endl;
       // #endif

        vec<Watched>::iterator i = ws.getData();
        vec<Watched>::iterator j = i;

        vec<Watched>::iterator end = ws.getDataEnd();
        for (; i != end; i++) {
            if (i->isBinary()) {
                *j++ = *i;
                if (!propBinaryClause<full>(i, p, confl)) break;
                else continue;
            } //end BINARY

            if (i->isTriClause()) {
                *j++ = *i;
                if (!propTriClause<full>(i, p, confl)) break;
                else continue;
            } //end TRICLAUSE

            if (i->isClause()) {
                num_props += 4;
                if (!propNormalClause<full>(i, j, p, confl, update)) break;
                else continue;
            } //end CLAUSE

            if (i->isXorClause()) {
                num_props += 10;
                if (!propXorClause<full>(i, j, p, confl)) break;
                else continue;
            } //end XORCLAUSE
        }
        if (i != end) {
            i++;
            //copy remaining watches
            vec<Watched>::iterator j2 = i;
            vec<Watched>::iterator i2 = j;
            for(i2 = i, j2 = j; i2 != end; i2++) {
                *j2++ = *i2;
            }
            //memmove(j, i, sizeof(Watched)*(end-i));
        }
        //assert(i >= j);
        ws.shrink_(i-j);
		
		if(conf.doPureliteral&&full&&dopurenow&&constructpure)
		{
		   if(qhead!=trail.size()){
		   //assert(p.toInt()<2*nVars()+1);
		   uint32_t which= p.toInt();
		   double   cpu_time2 = cpuTime();
		   purelit_proc(which);
		   //dopuretime+= cpuTime()- cpu_time2;
		   }
		 //  if(!reason[p.var()].isPurelit())
		   //printf("implied: %d\n", p.toInt());
		   //else
		   //printf("implied by pure: %d\n", p.toInt());
		}
    }
    propagations += num_props;
    simpDB_props -= num_props;

   // #ifdef VERBOSE_DEBUG
    //cout << "Propagation ended." << endl;
    //#endif
	chead=clause_trail.size();
    return confl;
}
template PropBy Solver::propagate<true>(const bool update);
template PropBy Solver::propagate<false>(const bool update);


// add by alanwnag
void Solver::purelit_proc(uint32_t clit)
 {
   vec<uint32_t>& theliteral=litcontain[clit];
   if(theliteral.size()==0) {
       /*vec<Watched>&  ws  = watches[(~(Lit::toLit(clit))).toInt()];
	   vec<Watched>::iterator i= ws.getData();
	   vec<Watched>::iterator end= ws.getDataEnd();
	   for(; i!=end; i++)
	   {
	      if(i->isBinary()&&!(i->getLearnt())){
			  Lit other =i->getOtherLit();
			  if(assigns[other.var()].isUndef()){
			  if(litcontain[other.toInt()].size()==0)
			  { checkbinandten(other.toInt());   }}
		  }
		  
		  else
		  {break;}
	   }*/
	   return;
   }
   //printf("in pure lit proc \n");
   for(uint32_t m=0; m<litcontain[clit].size(); m++)
   {
     uint32_t sat_clause_ind = theliteral[m];
	 //printf("%d \n", sat_clause_ind);
     if(clauses_cpy[sat_clause_ind]!=NULL)
     {
	    if((clauses_cpy[sat_clause_ind])->get_issat()==false)
		{
		  //assert(satby[sat_clause_ind]==lit_Undef.toInt());
		  (clauses_cpy[sat_clause_ind])->set_issat(true);
		  //(clauses_cpy[sat_clause_ind])->set_satby(Lit::toLit(clit));
		  satby[sat_clause_ind]=clit;
		   clause_trail.push(sat_clause_ind+1+2*nVars());
		  //trail.push(Lit::toLit(2*nVars()+1+sat_clause_ind));
		}
	 }
   } 
  // printf("out of pure lit proc \n");
}
// add by alanwang
void Solver::trytofindpurelit(uint32_t clause_ind)
{
//printf("in tryto\n");
    if(watch_c[clause_ind].size()>0)
	{
	   vec<uint32_t>& relate_lits=watch_c[clause_ind];
	   vec<uint32_t>::iterator k = relate_lits.getData();
       vec<uint32_t>::iterator j = k;
	   for(vec<uint32_t>::iterator  end = relate_lits.getDataEnd(); k != end; k++)
	   {
			 Lit ll=Lit::toLit(*k);
			 if(!candopure[ll.var()]) {continue;}
			 
			 if(assigns[ll.var()].isUndef()){
				 vec<uint32_t>& thelit= litcontain[(*k)];
				 bool findother=false;
				 if(thelit.size()>1)
				 {
					 vec<uint32_t>::iterator m = thelit.getData(); 
					 //assert(thelit[0]==clause_ind);
					 if(thelit[0]!=clause_ind) continue;
					// assert(clauses_cpy[thelit[0]]->get_cpyindex()==thelit[0]);
					// assert(clauses_cpy[*m]->get_issat());
					// assert(clauses_cpy[*m]!=NULL);
					 m++;
					 
					for(vec<uint32_t>::iterator end = thelit.getDataEnd(); m != end; m++)
					{
					   
					   if(clauses_cpy[(*m)]!=NULL)
					   {
						  Clause *c=clauses_cpy[(*m)];
						  if(!(c->get_issat()))
						  {
							uint32_t tmp=thelit[0];
							//assert(c->satby==lit_Undef);
							thelit[0]=*m;
							*m= tmp;
							findother=true;
							watch_c[thelit[0]].push((*k));
							break;
						  }
					   }
					}
				 }
				 if(!(thelit.size()>1)||!findother)
				 {
					checkbinandten(*k);
				 }
				 
				 if(!findother)
				 {*j++ = *k;}
				 // check binary && ternary clauses
			}
			else{*j++ = *k; }
	   }
	   relate_lits.shrink_(k-j);
	}
	//printf("out of try to\n");
}

/** 
@brief last step of find pure literal
check the binary and tenary clauses add by alanwang
*/
void Solver::checkbinandten(uint32_t checklit)
{
   // printf("in checkbin\n");
   if(!conf.doPureliteral) return;
   
    Lit thelit= Lit::toLit(checklit);
	
	//if(partHandler->getSavedState()[thelit.var()] != l_Undef) return;
	
	if(candopure[thelit.var()]&& assigns[thelit.var()].isUndef()){
	puresatby[checklit].clear();
	//assert(litcontain[checklit].size()==0);
	vec<Lit>& pure =puresatby[checklit];
	vec<Watched>&  ws  = watches[(~thelit).toInt()];
	vec<Watched>::iterator i = ws.getData();
    vec<Watched>::iterator end = ws.getDataEnd();
	//bool findpureliteral= false;
	bool findpureliteral= true;
    for (; i != end; i++) {
		if(!(i->isBinary()))
		{
		    //findpureliteral=true;
			/*if(i->isTriClause()&&!i->islearnt)
			{
			lbool val1=value(i->getOtherLit());
			lbool val2=value(i->getOtherLit2());
			assert((val1==l_True)||(val2==l_True));
			}
			else if(i->isClause())
			{
			    const uint32_t offset = i->getNormOffset();
				Clause& c = *clauseAllocator.getPointer(offset);
				if(!(c.learnt())){
				bool issat=false;
				for(uint32_t j=0;j<c.size();j++)
				{
					if(value(c[j])==l_True){ issat=true; break;}
				}
				assert(issat);}
			}*/
			//break;
			continue;
		}
		else
		{
		  //if(i->getLearnt()==false)
		 // {
			
			 lbool val = value(i->getOtherLit());
                 if (val==l_True) {
					pure.push(i->getOtherLit());
				    
			       }
			     else
				 {
				   pure.clear();
				   findpureliteral=false;
		          //  break;
				  return;
				 }
		 // }
		}
	}
	/*if(i==end){
		if(ws[ws.size()-1].isBinary())
		{
			findpureliteral=true;
		}
	}*/
	//assert(dopurenow);
	if(findpureliteral)
	{
	  //printf("begin propby \n");
	 
	  vec<Lit> pps ; pps.clear(); pps.push(~thelit);
	  vec<uint32_t> record; record.clear();
	  
	  pureseen[pps[0].toInt()]=true;
	  record.push(pps[0].toInt());
	  uint32_t ppsz		= litcontain[thelit.toInt()].size() + puresatby[thelit.toInt()].size();
	  vec<uint32_t>& tmp= litcontain[thelit.toInt()]; 
	  
	 
	  uint32_t max_level=0;
	  uint32_t min_level=nVars()+1;;
	  for(uint32_t ii=0;ii<ppsz;ii++)
	  {
		Lit put_in;
		
		if(ii<litcontain[thelit.toInt()].size()) {
		 Clause* ccr= clauses_cpy[tmp[ii]];
		 //assert(!(ccr->satby==lit_Undef));
		 if(ccr!=NULL){
		// assert(ccr->get_issat());
		put_in=(~(Lit::toLit(satby[tmp[ii]])));} }
        else {put_in=(~pure[ii-tmp.size()]);}
		//(c.size() == 3) ? c[2] : lit_Undef
		if(put_in!=lit_Undef)
		{
		   //if(level[put_in.var()]!=0)
		   //{
		   if(subsumer){
			   if (subsumer->getVarElimed()[put_in.var()] && !subsumer->unEliminate(put_in.var()))
					{
						for(uint32_t j=0; j<record.size(); j++)
					   {pureseen[record[j]]=false;}
					   return ;
					}
			}
            else if (xorSubsumer->getVarElimed()[put_in.var()] && !xorSubsumer->unEliminate(put_in.var()))
               { 
			   			for(uint32_t j=0; j<record.size(); j++)
					   {pureseen[record[j]]=false;}
					   return ;
			   }	
				
		        //assert(value(put_in)==l_False);
				if(pureseen[(~put_in).toInt()])
				{return;}
				
				else if(!pureseen[put_in.toInt()])
				{
				    pps.push(put_in);
				    pureseen[put_in.toInt()]=true;
					//pureseen[(~put_in).toInt()]=true;
				    record.push(put_in.toInt());
					//record.push((~put_in).toInt());
					if(level[put_in.var()]>max_level) max_level=level[put_in.var()];
					if(level[put_in.var()]<min_level) min_level=level[put_in.var()];
				}
			
		   //}
		}
	  }
	  for(uint32_t j=0; j<record.size(); j++)
		{pureseen[record[j]]=false;}
	 // uint32_t old_clause_sz=clauses.size();
	 //printf("pps size():%d \n", pps.size());
	  /*
	  Clause* c = clauseAllocator.Clause_new(ps, group);
        if (learnt) c->makeLearnt(glue, miniSatActivity);
        attachClause(*c);
        return c;
    } else {
        attachBinClause(ps[0], ps[1], learnt);
        if (!inOriginalInput) dataSync->signalNewBinClause(ps);
        numNewBin++;*/
	  if( pps.size()<2)
	  {return;}
	  //printf("max-min level=%d\n", max_level-min_level);
	  //if(!conf.doPartHandler&&(max_level-min_level)>30) return;
	  if((max_level-min_level)>conf.level_diff) return;
	  //addClause(pps);
	  Clause * ccc=NULL;
	  if(pps.size()>2)
	  { ccc=clauseAllocator.Clause_new(pps,  false);
	    clauses.push(ccc);
		addpurestruc(ccc);
	  }
	  
	  
	  //if(old_clause_sz<clauses.size())
	  //{
	  //	 assert(pps.size()>2);
	  //ccc	= clauses[old_clause_sz];
		
	  //}
	  
	   PropBy pp;
	   uint32_t kkk = pps.size();
	   if( kkk == 2)
	   {
			
			 //dataSync->signalNewBinClause(pps);
			 numNewBin++;
			 attachBinClause(pps[0], pps[1], false);
			 num_pureliteral++;
			

		//if(watches[(~pps[0]).toInt()].size()>1){std::sort(watches[(~pps[0]).toInt()].getData(),watches[(~pps[0]).toInt()].getDataEnd(), WatchedSorter());}
        //if(watches[(~pps[1]).toInt()].size()>1){std::sort(watches[(~pps[1]).toInt()].getData(),watches[(~pps[1]).toInt()].getDataEnd(), WatchedSorter());}
		
		////// /////////////////////////////////////////////////////////////////////////////////////////////////
		uncheckedEnqueue( ~thelit, PropBy(pps[1]));
	   }
	   else if( kkk == 3 )
	   {
			attachClause(*ccc);
			////////////////////////
			uncheckedEnqueue( ~thelit,PropBy(pps[1], pps[2]));
			num_pureliteral++;
	   }
       else if( kkk>3)
	   {
		   //assert(kkk>2);
		   //assert(ccc!=NULL);
		   
		   const uint32_t offset=clauseAllocator.getOffset(ccc);
		   attachClause(*ccc);
		   ////////////////////////////////////////////////////
		   uncheckedEnqueue( ~thelit,PropBy(offset));
		   num_pureliteral++;
	   }
    
	   
	  //printf("propby: %d \n ", (~thelit).toInt());
	  
	  
	  
	  
	  //candopure[thelit.var()]=false;
	}
	}
	//printf("out of checkbin\n");
}

// add by alanwang
void Solver::addpurestruc(Clause * cc)
{
   //assert(cc->size()>2);
   cc->set_cpyindex(clauses_cpy.size());
   cc->set_issat(false);
   uint32_t level_now=nVars();
   
   //for(uint32_t i=0;i<cc->size();i++){
    //assert(value((*cc)[i])!=l_True);
	//printf("%d ", (*cc)[i].toInt());
	/* if(value((*cc)[i])==l_True)
	   {
		  if(level[(*cc)[i].var()]<level_now)
		  {
		    level_now=level[(*cc)[i].var()];
			cc->cpy_issat=true;
			cc->satby=(*cc)[i];
		  }
	   }*/
   //}
   //printf("\n");
   clauses_cpy.push(cc);
   satby.push(lit_Undef.toInt());
   //assert(clasue);
   //assert(cc==clauses_cpy[cc->cpy_index]);
   //assert(qhead==trail.size());
   /*if(cc->cpy_issat)
   {
    trail.push(Lit::toLit(2*nVars()+1+cc->cpy_index));
	qhead++;
   
   }*/
  // vec<uint32_t> son; 
  // son.push(0);
  //watch_c.push(vec<uint32_t> );
   watch_c.growTo(clauses_cpy.size());
   //assert(watch_c.size()== clauses_cpy.size());
   //assert(watch_c[1].size());
   watch_c[cc->get_cpyindex()].clear();
   for(uint32_t i=0;i<(cc->size());i++)
   {
		litcontain[(*cc)[i].toInt()].push(cc->get_cpyindex());
		if(litcontain[(*cc)[i].toInt()].size()==1)
		{
		    watch_c[cc->get_cpyindex()].push((*cc)[i].toInt());
		}
   }
}

PropBy Solver::propagateBin(vec<Lit>& uselessBin)
{
    //#ifdef DEBUG_USELESS_LEARNT_BIN_REMOVAL
    //assert(uselessBin.empty());
    //#endif

    while (qhead < trail.size()) {
        Lit p = trail[qhead++];

        //setting up binPropData
        uint32_t lev = binPropData[p.var()].lev;
        Lit lev1Ancestor;
        switch (lev) {
            case 0 :
                lev1Ancestor = lit_Undef;
                break;
            case 1:
                lev1Ancestor = p;
                break;
            default:
                lev1Ancestor = binPropData[p.var()].lev1Ancestor;
        }
        lev++;
        const bool learntLeadHere = binPropData[p.var()].learntLeadHere;
        bool& hasChildren = binPropData[p.var()].hasChildren;
        hasChildren = false;

        //std::cout << "lev: " << lev << " ~p: "  << ~p << std::endl;
        const vec<Watched> & ws = watches[p.toInt()];
        propagations += 2;
        for(vec<Watched>::const_iterator k = ws.getData(), end = ws.getDataEnd(); k != end; k++) {
            hasChildren = true;
            if (!k->isBinary()) continue;

            //std::cout << (~p) << ", " << k->getOtherLit() << " learnt: " << k->getLearnt() << std::endl;
            lbool val = value(k->getOtherLit());
            if (val.isUndef()) {
                uncheckedEnqueueLight2(k->getOtherLit(), lev, lev1Ancestor, learntLeadHere || k->getLearnt());
            } else if (val == l_False) {
                return PropBy(p);
            } else {
                //assert(val == l_True);
                Lit lit2 = k->getOtherLit();
                if (lev > 1
                    && level[lit2.var()] != 0
                    && binPropData[lit2.var()].lev == 1
                    && lev1Ancestor != lit2) {
                    //Was propagated at level 1, and again here, original level 1 binary clause is useless
                    binPropData[lit2.var()].lev = lev;
                    binPropData[lit2.var()].lev1Ancestor = lev1Ancestor;
                    binPropData[lit2.var()].learntLeadHere = learntLeadHere || k->getLearnt();
                    uselessBin.push(lit2);
                }
            }
        }
    }
    //std::cout << " -----------" << std::endl;

    return PropBy();
}

/**
@brief Only propagates binary clauses

This is used in special algorithms outside the main Solver class
*/
PropBy Solver::propagateNonLearntBin()
{
    multiLevelProp = false;
    uint32_t origQhead = qhead + 1;

    while (qhead < trail.size()) {
        Lit p = trail[qhead++];
        const vec<Watched> & ws = watches[p.toInt()];
        propagations += ws.size()/2 + 2;
        for(vec<Watched>::const_iterator k = ws.getData(), end = ws.getDataEnd(); k != end; k++) {
            if (!k->isNonLearntBinary()) break;

            lbool val = value(k->getOtherLit());
            if (val.isUndef()) {
                if (qhead != origQhead) multiLevelProp = true;
                uncheckedEnqueueLight(k->getOtherLit());
            } else if (val == l_False) {
                return PropBy(p);
            }
        }
    }

    return PropBy();
}

/**
@brief Propagate recursively on non-learnt binaries, but do not propagate exceptLit if we reach it
*/
bool Solver::propagateBinExcept(const Lit exceptLit)
{
    while (qhead < trail.size()) {
        Lit p   = trail[qhead++];
        const vec<Watched> & ws = watches[p.toInt()];
        propagations += ws.size()/2 + 2;
        for(vec<Watched>::const_iterator i = ws.getData(), end = ws.getDataEnd(); i != end; i++) {
            if (!i->isNonLearntBinary()) break;

            lbool val = value(i->getOtherLit());
            if (val.isUndef() && i->getOtherLit() != exceptLit) {
                uncheckedEnqueueLight(i->getOtherLit());
            } else if (val == l_False) {
                return false;
            }
        }
    }

    return true;
}

/**
@brief Propagate only for one hop(=non-recursively) on non-learnt bins
*/
bool Solver::propagateBinOneLevel()
{
    Lit p   = trail[qhead];
    const vec<Watched> & ws = watches[p.toInt()];
    propagations += ws.size()/2 + 2;
    for(vec<Watched>::const_iterator i = ws.getData(), end = ws.getDataEnd(); i != end; i++) {
        if (!i->isNonLearntBinary()) break;

        lbool val = value(i->getOtherLit());
        if (val.isUndef()) {
            uncheckedEnqueueLight(i->getOtherLit());
        } else if (val == l_False) {
            return false;
        }
    }

    return true;
}

struct LevelSorter
{
    LevelSorter(const vec<int32_t>& _level) :
        level(_level)
    {}

    bool operator()(const Lit lit1, const Lit lit2) const {
        return level[lit1.var()] < level[lit2.var()];
    }

    const vec<int32_t>& level;
};

/**
@brief Calculates the glue of a clause

Used to calculate the Glue of a new clause, or to update the glue of an
existing clause. Only used if the glue-based activity heuristic is enabled,
i.e. if we are in GLUCOSE mode (not MiniSat mode)
*/
template<class T>
inline uint32_t Solver::calcNBLevels(const T& ps)
{
    uint32_t nbLevels = 0;
    for(const Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
        int32_t lev = level[l->var()];
        if (!seen[lev]) {
            nbLevels++;
            seen[lev] = 1;
        }
    }
    for(const Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
        int32_t lev = level[l->var()];
        seen[lev] = 0;
    }
    return nbLevels;
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
bool  reduceDB_ltMiniSat::operator () (const Clause* x, const Clause* y) {
    const uint32_t xsize = x->size();
    const uint32_t ysize = y->size();

    //assert(xsize > 2 && ysize > 2);
    if (x->getMiniSatAct() == y->getMiniSatAct())
        return xsize > ysize;
    else return x->getMiniSatAct() < y->getMiniSatAct();
}

bool  reduceDB_ltGlucose::operator () (const Clause* x, const Clause* y) {
    const uint32_t xsize = x->size();
    const uint32_t ysize = y->size();

    //assert(xsize > 2 && ysize > 2);
    if (x->getGlue() > y->getGlue()) return 1;
    if (x->getGlue() < y->getGlue()) return 0;
    return xsize > ysize;
}

/**
@brief Removes learnt clauses that have been found not to be too good

Either based on glue or MiniSat-style learnt clause activities, the clauses are
sorted and then removed
*/
void Solver::reduceDB()
{
    uint32_t     i, j;

    nbReduceDB++;
    if (lastSelectedRestartType == dynamic_restart)
        std::sort(learnts.getData(), learnts.getDataEnd(), reduceDB_ltGlucose());
    else
        std::sort(learnts.getData(), learnts.getDataEnd(), reduceDB_ltMiniSat());

    #ifdef VERBOSE_DEBUG
    std::cout << "Cleaning clauses" << std::endl;
    for (uint32_t i = 0; i != learnts.size(); i++) {
        std::cout << "activity:" << learnts[i]->getGlue()
        << " \toldActivity:" << learnts[i]->getMiniSatAct()
        << " \tsize:" << learnts[i]->size() << std::endl;
    }
    #endif


    //const uint32_t removeNum = (double)learnts.size() * (double)RATIOREMOVECLAUSES;
	
	
	 //const uint32_t removeNum = ( (double)learnts.size() * (double)RATIOREMOVECLAUSES ); // delete by hankf4
	double szz=(double)learnts.size();
	//if(conf.doXordynamic) szz-=((double)additional_morexor+(double)additional_one);
     uint32_t removeNum = (uint32_t) (szz * (double)RATIOREMOVECLAUSES   ); // modify by hankf4
	 
	// if(removeNum>3*num_purelearnt) removeNum-= (uint32_t)(3*(double)num_purelearnt);  //modify by alanwang
	//else removeNum=0;   // modify by alanwang
	 
    uint32_t totalNumRemoved = 0;
    uint32_t totalNumNonRemoved = 0;
    uint64_t totalGlueOfRemoved = 0;
    uint64_t totalSizeOfRemoved = 0;
    uint64_t totalGlueOfNonRemoved = 0;
    uint64_t totalSizeOfNonRemoved = 0;
    for (i = j = 0; i != removeNum; i++){
        if (i+1 < removeNum) __builtin_prefetch(learnts[i+1]);
        //assert(learnts[i]->size() > 2);
        if (!locked(*learnts[i])
            && (lastSelectedRestartType == static_restart || learnts[i]->getGlue() > 2)
            && learnts[i]->size() > 3) { //we cannot update activity of 3-longs because of wathclists

            totalGlueOfRemoved += learnts[i]->getGlue();
            totalSizeOfRemoved += learnts[i]->size();
            totalNumRemoved++;
            removeClause(*learnts[i]);
        } else {
            totalGlueOfNonRemoved += learnts[i]->getGlue();
            totalSizeOfNonRemoved += learnts[i]->size();
            totalNumNonRemoved++;
            learnts[j++] = learnts[i];
        }
    }
    for (; i < learnts.size(); i++) {
        totalGlueOfNonRemoved += learnts[i]->getGlue();
        totalSizeOfNonRemoved += learnts[i]->size();
        totalNumNonRemoved++;
        learnts[j++] = learnts[i];
    }
    learnts.shrink_(i - j);

    if (conf.verbosity >= 3) {
        std::cout << "c rem-learnts " << std::setw(6) << totalNumRemoved
        << "  avgGlue "
        << std::fixed << std::setw(5) << std::setprecision(2)  << ((double)totalGlueOfRemoved/(double)totalNumRemoved)
        << "  avgSize "
        << std::fixed << std::setw(6) << std::setprecision(2) << ((double)totalSizeOfRemoved/(double)totalNumRemoved)
        << "  || remain " << std::setw(6) << totalNumNonRemoved
        << "  avgGlue "
        << std::fixed << std::setw(5) << std::setprecision(2)  << ((double)totalGlueOfNonRemoved/(double)totalNumNonRemoved)
        << "  avgSize "
        << std::fixed << std::setw(6) << std::setprecision(2) << ((double)totalSizeOfNonRemoved/(double)totalNumNonRemoved)
        << std::endl;
    }

    clauseAllocator.consolidate(this);
}

inline int64_t abs64(int64_t a)
{
    if (a < 0) return -a;
    return a;
}

/**
@brief Simplify the clause database according to the current top-level assigment.

We remove satisfied clauses, clean clauses from assigned literals, find
binary xor-clauses and replace variables with one another. Heuristics are
used to check if we need to find binary xor clauses or not.
*/
bool Solver::simplify()
{
    testAllClauseAttach();
    //assert(decisionLevel() == 0);

    if (!ok || !propagate<false>().isNULL()) {
        ok = false;
        return false;
    }

    if (simpDB_props > 0) {
        return true;
    }
    double myTime = cpuTime();

    double slowdown = (100000.0/((double)numBins * 30000.0/((double)order_heap.size())));
    slowdown = std::min(1.5, slowdown);
    slowdown = std::max(0.01, slowdown);

    double speedup = 200000000.0/(double)(propagations-lastSearchForBinaryXor);
    speedup = std::min(3.5, speedup);
    speedup = std::max(0.2, speedup);

    /*std::cout << "new:" << nbBin - lastNbBin + becameBinary << std::endl;
    std::cout << "left:" << ((double)(nbBin - lastNbBin + becameBinary)/BINARY_TO_XOR_APPROX) * slowdown  << std::endl;
    std::cout << "right:" << (double)order_heap.size() * PERCENTAGEPERFORMREPLACE * speedup << std::endl;*/

    if (conf.doFindEqLits && conf.doRegFindEqLits &&
        (((double)abs64((int64_t)numNewBin - (int64_t)lastNbBin)/BINARY_TO_XOR_APPROX) * slowdown) >
        ((double)order_heap.size() * PERCENTAGEPERFORMREPLACE * speedup)) {
        lastSearchForBinaryXor = propagations;

        clauseCleaner->cleanClauses(clauses, ClauseCleaner::clauses);
        clauseCleaner->cleanClauses(learnts, ClauseCleaner::learnts);
        clauseCleaner->removeSatisfiedBins();
        if (!ok) return false;

        if (!sCCFinder->find2LongXors()) return false;

        lastNbBin = numNewBin;
    }

    // Remove satisfied clauses:
    clauseCleaner->removeAndCleanAll();
    if (!ok) return false;

    if (conf.doReplace && !varReplacer->performReplace())
        return false;

    // Remove fixed variables from the variable heap:
    order_heap.filter(VarFilter(*this));

    #ifdef USE_GAUSS
   // for (vector<Gaussian*>::iterator gauss = gauss_matrixes.begin(), end = gauss_matrixes.end(); gauss != end; gauss++) {
   //     if (!(*gauss)->full_init()) return false;
   //}
   /*
   for (vector<EnhanceGaussian*>::iterator gauss = EnhancGauss_matrixes.begin(), end = EnhancGauss_matrixes.end(); gauss != end; gauss++) {
		//printf("DD:simply\n");
		if (!(*gauss)->full_init()) 
            return false;	
	}  */
    #endif //USE_GAUSS

	#ifdef USE_GAUSS		
	big_gaussnum = 0;
	big_propagate = 0;
	big_conflict = 0;	
	engaus_disable = false;
	#endif //USE_GAUSS
	
	
	
    simpDB_assigns = nAssigns();
    simpDB_props = std::min((uint64_t)80000000, 4*clauses_literals + 4*learnts_literals); //at most 6 sec wait
    simpDB_props = std::max((int64_t)30000000, simpDB_props); //at least 2 sec wait
    totalSimplifyTime += cpuTime() - myTime;

    testAllClauseAttach();
    return true;
}
/**
@brief Does the Gause eliminateion

Add by hankf4
*/

inline llbool Solver::Gauss_elimination(vec<Lit>& learnt_clause, uint64_t& conflictC)
{

	bool do_eliminate = false;
	bool enter_matrix = false;
	Var e_var;
	uint16_t e_row_n ;
	uint16_t matrix_id = 0;
	PropBy confl;	
	//assert(qhead == trail.size());
	//assert(Gauseqhead <= qhead);
	

	
 	if( big_gaussnum > 50 && big_conflict*2+big_propagate < (uint32_t)((double)big_gaussnum*0.05 ) ){  
		engaus_disable = true;
	}
	
 	if( engaus_disable
		|| (decisionLevel() > gaussconfig.decision_until) )
		return l_Nothing; 
	
	
	while (Gauseqhead <  trail.size() ) {
        Lit p   = trail[Gauseqhead++];     // 'p' is enqueued fact to propagate.
   
		vec<GausWatched>&  ws  = GausWatches[p.var()];
		vec<GausWatched>::iterator i = ws.getData();
		vec<GausWatched>::iterator j = i;
		vec<GausWatched>::iterator end = ws.getDataEnd();
		
		if(i != end)
			matrix_id = (*i).matrix_num;
		else
			continue ;
		
		enter_matrix = true;
		for (; i != end; i++) {
			assert(matrix_id == (*i).matrix_num);
/* 			if(EnhancGauss_matrixes[matrix_id]->find_truths( i ,j , p.var()  , confl ,(*i).row_id ,do_eliminate , e_var , e_row_n ))
				continue;
			else{
				break;
			} */
			
			if(gaussconfig.add_learn_three >= 1 ) {
				if(EnhancGauss_matrixes[matrix_id]->find_truths3( i ,j , p.var()  , confl ,(*i).row_id ,do_eliminate , e_var , e_row_n )){
						continue;
				}
				else{ // only in conflict two variable
					break;
				}
			}else{
				if(EnhancGauss_matrixes[matrix_id]->find_truths( i ,j , p.var()  , confl ,(*i).row_id ,do_eliminate , e_var , e_row_n )){
						continue;
				}
				else{ // only in conflict two variable
					break;
				}
			}
		}
		
		if (i != end) {  // must conflict
			//debug_size2 = ws.size();
			i++;
			//copy remaining watches
			vec<GausWatched>::iterator j2 = i;
			vec<GausWatched>::iterator i2 = j;
			
			for(i2 = i, j2 = j; i2 != end; i2++) {	
				*j2 = *i2;
				j2++;
			}
		}
		//assert(i >= j);
		ws.shrink_(i-j);
		
		if(do_eliminate){
			if(gaussconfig.add_learn_three >= 1) 
				EnhancGauss_matrixes[matrix_id]->eliminate_col3(e_var , e_row_n , p.var() ,confl);	
			else
				EnhancGauss_matrixes[matrix_id]->eliminate_col(e_var , e_row_n , p.var() ,confl);	
		}	
	}
	
	if(enter_matrix){
		big_gaussnum++; sum_Encalled++;
	}
	
	if (!confl.isNULL()) {    // conflict
		llbool ret = handle_conflict(learnt_clause, confl, conflictC, true);
		big_conflict++;
		sum_Enconflict++;
		
		if (confl.isClause())
			clauseAllocator.clauseFree(clauseAllocator.getPointer(confl.getClause())); 
		if (ret != l_Nothing) return ret;
		return l_Continue;
	}else if( qhead != trail.size() ){  // propagation  
		
		big_propagate++;
		sum_Enpropagate++;
		
		return l_Continue;;
	}
	return l_Nothing;
}
/**
@brief Search for a model

Limits: must be below the specified number of conflicts and must keep the
number of learnt clauses below the provided limit

Use negative value for 'nof_conflicts' or 'nof_learnts' to indicate infinity.

Output: 'l_True' if a partial assigment that is consistent with respect to the
clauseset is found. If all variables are decision variables, this means
that the clause set is satisfiable. 'l_False' if the clause set is
unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
*/
lbool Solver::search(
    const uint64_t nof_conflicts
    , const uint64_t nof_conflicts_fullrestart
    , const bool update
) {
    //assert(ok);
    uint64_t    conflictC = 0;
    vec<Lit>    learnt_clause;
    llbool      ret;
    double  gausstime;
    if (!simplifying && update) {
        /*if (conf.verbosity >= 4) {
            std::cout
            << "c RESTART"
            << " starts: " << starts
            << " dynStarts: " << dynStarts
            << " staticStarts: " << staticStarts
            << " nof_conflicts: " << nof_conflicts
            << " nof_conflicts_fullrestart: " << nof_conflicts_fullrestart
            << " fullStarts: " << fullStarts
            << " conflicts: " << conflicts
            << " starts: " << starts
            << std::endl;
        }*/
        
		///add by alanwang
		 starts++;
        if (restartType == static_restart)
		{
		   if(conf.doPureliteral)
		   {
			   if(!dopurenow)
				{staticStarts++;
				 staticStarts_ori++;
				}
				else
				{staticStarts_ori++;}
			}
			else
			{
			    staticStarts++;
			}
		}
        else dynStarts++;
		
		
    }////////
    glueHistory.fastclear();

    #ifdef USE_GAUSS
    /*for (vector<Gaussian*>::iterator gauss = gauss_matrixes.begin(), end = gauss_matrixes.end(); gauss != end; gauss++) {
        if (!(*gauss)->full_init())
            return l_False;
    }*/
	big_gaussnum = 0;
	big_propagate = 0;
	big_conflict = 0;	
	engaus_disable = false; 
    #endif //USE_GAUSS

    testAllClauseAttach();
    findAllAttach();
	
	if (decisionLevel() == 0) {
        if (dataSync&&!dataSync->syncData()) return l_False;
        if (!simplify()) return l_False;
    }
    #ifdef VERBOSE_DEBUG
    std::cout << "c started Solver::search()" << std::endl;
    //printAllClauses();
    #endif //VERBOSE_DEBUG
    for (;;) {
        //assert(ok);
		Gauseqhead = qhead; // add by hankf4
        PropBy confl = propagate<true>(update);
        #ifdef VERBOSE_DEBUG
        std::cout << "c Solver::search() has finished propagation" << std::endl;
        //printAllClauses();
        #endif //VERBOSE_DEBUG

        if (conflicts > conf.maxConfl) {
            /*if (conf.verbosity >= 0) {
                std::cout << "c Interrupting: limit on number of conflicts, "
                << conf.maxConfl
                << " reached! " << std::endl;
            }*/
            needToInterrupt = true;
            return l_Undef;
        }

        if (!confl.isNULL()) {
            ret = handle_conflict(learnt_clause, confl, conflictC, update);
            if (ret != l_Nothing) return ret;
        } else {
            #ifdef USE_GAUSS
           if ( EnhancGauss_matrixes_size > 0  && !engaus_disable){
				
				gausstime = cpuTime();
				ret = Gauss_elimination(learnt_clause, conflictC);
				Total_gauss_time += cpuTime() - gausstime;
				
				if (ret == l_Continue) continue;
				else if (ret != l_Nothing) return ret; 
			}   
            #endif //USE_GAUSS

            assert(ok);
            if (conf.doCacheOTFSSR  && decisionLevel() == 1) saveOTFData();
            ret = new_decision(nof_conflicts, nof_conflicts_fullrestart, conflictC);
            if (ret != l_Nothing) return ret;
        }
    }
}

/**
@brief Picks a new decision variable to branch on

@returns l_Undef if it should restart instead. l_False if it reached UNSAT
         (through simplification)
*/
llbool Solver::new_decision(const uint64_t nof_conflicts, const uint64_t nof_conflicts_fullrestart, const uint64_t conflictC)
{

    if (conflicts >= nof_conflicts_fullrestart || needToInterrupt)  {
        cancelUntil(0);
        return l_Undef;
    }

    // Reached bound on number of conflicts?
    switch (restartType) {
    case dynamic_restart:
        if (glueHistory.isvalid() &&
            0.95*glueHistory.getAvgDouble() > glueHistory.getAvgAllDouble()) {

            #ifdef DEBUG_DYNAMIC_RESTART
            if (glueHistory.isvalid()) {
                std::cout << "glueHistory.getavg():" << glueHistory.getavg() <<std::endl;
                std::cout << "totalSumOfGlue:" << totalSumOfGlue << std::endl;
                std::cout << "conflicts:" << conflicts<< std::endl;
                std::cout << "compTotSumGlue:" << compTotSumGlue << std::endl;
                std::cout << "conflicts-compTotSumGlue:" << conflicts-compTotSumGlue<< std::endl;
            }
            #endif

            cancelUntil(0);
            return l_Undef;
        }
        break;
    case static_restart:
        if (conflictC >= nof_conflicts) {
            cancelUntil(0);
            return l_Undef;
        }
        break;
    case auto_restart:
        assert(false);
        break;
    }

    // Simplify the set of problem clauses:
    if (decisionLevel() == 0) {
        if (dataSync && !dataSync->syncData()) return l_False;
        if (!simplify()) return l_False;
    }

    // Reduce the set of learnt clauses:
    //if (conflicts >= numCleanedLearnts * nbClBeforeRed + nbCompensateSubsumer) {
    //    numCleanedLearnts ++;
    //    reduceDB();
    //    nbClBeforeRed += 500;
    //}
    // delete by alanwang
	if(conf.doXordynamic){
	    //if(lockstat==0){
		if (conflicts >=num_purelearnt*5+(numCleanedLearnts * nbClBeforeRed + nbCompensateSubsumer+(additional_morexor+additional_one+additional_two)*additional_mut) ){
			numCleanedLearnts ++;
			reduceDB();
			
			if(additional_one_last-additional_one==0) additional_mut-=3;
			else {additional_mut=numCleanedLearnts*4+additional_mut_ori;}
			if(additional_mut>25) additional_mut=25;
			else if (additional_mut<additional_mut_ori) additional_mut=additional_mut_ori;
	if((additional_morexor+additional_one)>100&& additional_mut>10&&additional_one_last-additional_one!=0) additional_mut=additional_mut_ori;
			
			nbClBeforeRed +=  500;
			additional_one_last=additional_one;
		}
		//}
		//else lockstat--;
	}
    else
	{
		   if (conflicts >= (numCleanedLearnts * nbClBeforeRed + nbCompensateSubsumer)+num_purelearnt*5) {
			numCleanedLearnts ++;
			reduceDB();
			
			nbClBeforeRed +=  500;
		}
	
	}
	
	
    Lit next = lit_Undef;
    while (decisionLevel() < assumptions.size()) {
        // Perform user provided assumption:
        Lit p = assumptions[decisionLevel()];
		candopure[p.var()]=false;
        if (value(p) == l_True) {
            // Dummy decision level:
            newDecisionLevel();

            //To store matrix in case it needs to be stored. No new information is meant to be available at this point.
            #ifdef USE_GAUSS
            //These are not supposed to be changed *at all* by the funciton
            //since it has already been called before
            vec<Lit>    learnt_clause;
            uint64_t conflictC;

           // for (vector<Gaussian*>::iterator gauss = gauss_matrixes.begin(), end= gauss_matrixes.end(); gauss != end; gauss++) {
            //    llbool ret = (*gauss)->find_truths(learnt_clause, conflictC);
             //   assert(ret == l_Nothing);
            //}
			  llbool ret =Gauss_elimination(learnt_clause, conflictC);
			 // assert(ret == l_Nothing);
            #endif //USE_GAUSS


        } else if (value(p) == l_False) {
            analyzeFinal(~p, conflict);
            return l_False;
        } else {
            next = p;
            break;
        }
    }

    if (next == lit_Undef) {
        // New variable decision:
        decisions++;
        next = pickBranchLit();

        if (next == lit_Undef)
            return l_True;
    }

    // Increase decision level and enqueue 'next'
    //assert(value(next) == l_Undef);
    newDecisionLevel();
    uncheckedEnqueue(next);

    return l_Nothing;
}

#ifdef HAVE_MYSQL
void Solver::addClauseToMySQL(const vec<Lit>& clause, const bool learnt, const uint32_t glue)
{
    if (!conf.serverConn || !insSTMTLits.STMT)
        return;

    //Add general clause info
    insSTMTCl.decLevel = decisionLevel();
    insSTMTCl.glue = glue;
    insSTMTCl.learnt = learnt;
    insSTMTCl.num = mysqClauseNum++;
    insSTMTCl.size = clause.size();
    insSTMTCl.trailLevel = trail.size();
    if (mysql_stmt_execute(insSTMTCl.STMT)) {
        std::cout << "mysql_stmt_execute(), 1 failed" << std::endl
        << mysql_stmt_error(insSTMTCl.STMT) << std::endl;
        exit(1);
    }

    //Get autoinc value
    my_ulonglong autoInc = mysql_insert_id(conf.serverConn);
    //assert(autoInc != 0);
    insSTMTLits.autoInc = autoInc;

    //add literals of the clause
    for(size_t i = 0; i < clause.size(); i++) {
        insSTMTLits.litVar = clause[i].var();
        insSTMTLits.inverted = clause[i].sign();

        // Execute the INSERT statement
        if (mysql_stmt_execute(insSTMTLits.STMT)) {
            std::cout << "mysql_stmt_execute(), 1 failed" << std::endl
            << mysql_stmt_error(insSTMTLits.STMT) << std::endl;
            exit(1);
        }

        /* Get the number of affected rows */
        int affected_rows= mysql_stmt_affected_rows(insSTMTLits.STMT);

        // validate affected rows
        if (affected_rows != 1)  {
          std::cout << "invalid affected rows by MySQL" << std::endl;
          exit(1);
        }
    }
}
#endif

/**
@brief Handles a conflict that we reached through propagation

Handles on-the-fly subsumption: the OTF subsumption check is done in
conflict analysis, but this is the code that actually replaces the original
clause with that of the shorter one
@returns l_False if UNSAT
*/
llbool Solver::handle_conflict(vec<Lit>& learnt_clause, PropBy confl, uint64_t& conflictC, const bool update)
{
    //#ifdef VERBOSE_DEBUG
    //cout << "Handling conflict: ";
    //for (uint32_t i = 0; i < learnt_clause.size(); i++)
    //    cout << learnt_clause[i].var()+1 << ",";
    //cout << endl;
    //#endif

    int backtrack_level;
    uint32_t glue;

    conflicts++;
    conflictC++;
    if (decisionLevel() == 0)
        return l_False;
    learnt_clause.clear();
    Clause* c = analyze(confl, learnt_clause, backtrack_level, glue, update);
    if (update) {
        avgBranchDepth.push(decisionLevel());
        if (restartType == dynamic_restart) glueHistory.push(glue);
        conflSizeHist.push(learnt_clause.size());
    }
#ifdef HAVE_MYSQL
    addClauseToMySQL(learnt_clause, true, glue);
#endif //HAVE_MYSQL

    cancelUntil(backtrack_level);
   // #ifdef DUMP_STATS
   // std::cout << "Learnt clause: " << learnt_clause
  //  << " glue: " << glue
  //  << " declevel: " << decisionLevel()
  //  << " traillen: " << trail.size()
  //  << " abst: " << calcAbstraction(learnt_clause)
  //  << std::endl;
   // assert(learnt_clause.size() == 1 || glue > 1);
  //  #endif //#ifdef DUMP_STATS

  //  #ifdef VERBOSE_DEBUG
   // cout << "Learning:";
  //  for (uint32_t i = 0; i < learnt_clause.size(); i++) printLit(learnt_clause[i]), cout << " ";
  //  cout << endl;
  //  cout << "reverting var " << learnt_clause[0].var()+1 << " to " << !learnt_clause[0].sign() << endl;
  //  #endif
//
   // assert(value(learnt_clause[0]) == l_Undef);
    //Unitary learnt
    if (learnt_clause.size() == 1) {
        uncheckedEnqueue(learnt_clause[0]);
     //   assert(backtrack_level == 0 && "Unit clause learnt, so must cancel until level 0, right?");

      //  #ifdef VERBOSE_DEBUG
     //   cout << "Unit clause learnt." << endl;
     //   #endif
    //Normal learnt
    } else {
        if (learnt_clause.size() == 2) {
            attachBinClause(learnt_clause[0], learnt_clause[1], true);
            numNewBin++;
            if (dataSync) {
                dataSync->signalNewBinClause(learnt_clause);
            }
            uncheckedEnqueue(learnt_clause[0], PropBy(learnt_clause[1]));
            goto end;
        }

        if (learnt_clause.size() > 3) {
            std::sort(learnt_clause.getData()+1, learnt_clause.getDataEnd(), PolaritySorter(polarity));
        }
        if (c) { //On-the-fly subsumption
            uint32_t origSize = c->size();
            detachClause(*c);
            for (uint32_t i = 0; i != learnt_clause.size(); i++)
                (*c)[i] = learnt_clause[i];
            c->shrink(origSize - learnt_clause.size());
            if (c->learnt() && c->getGlue() > glue)
                c->setGlue(glue); // LS
            attachClause(*c);
            uncheckedEnqueue(learnt_clause[0], clauseAllocator.getOffset(c));
        } else {  //no on-the-fly subsumption
            c = clauseAllocator.Clause_new(learnt_clause, true);
            #ifdef ENABLE_UNWIND_GLUE
            if (conf.doMaxGlueDel && glue > conf.maxGlue) {
                nbClOverMaxGlue++;
                nbCompensateSubsumer++;
                unWindGlue[learnt_clause[0].var()] = c;
                #ifdef UNWINDING_DEBUG
                std::cout << "unwind, var:" << learnt_clause[0].var() << std::endl;
                c->plainPrint();
                #endif //VERBOSE_DEBUG
            } else {
                #endif //ENABLE_UNWIND_GLUE
                learnts.push(c);
				if(dopurenow) {num_purelearnt++;}
                #ifdef ENABLE_UNWIND_GLUE
            }
            #endif //ENABLE_UNWIND_GLUE
            c->setGlue(std::min(glue, MAX_THEORETICAL_GLUE));
            attachClause(*c);
            uncheckedEnqueue(learnt_clause[0], clauseAllocator.getOffset(c));
        }
        end:;
    }

    varDecayActivity();
    if (update && restartType == static_restart) claDecayActivity();

    return l_Nothing;
}

/**
@brief After a full restart, determines which restar type to use

Uses class RestartTypeChooser to do the heavy-lifting
*/
bool Solver::chooseRestartType(const uint32_t& lastFullRestart)
{
    uint32_t relativeStart = starts - lastFullRestart;

    if (relativeStart > RESTART_TYPE_DECIDER_FROM  && relativeStart < RESTART_TYPE_DECIDER_UNTIL) {
        if (conf.fixRestartType == auto_restart)
            restartTypeChooser->addInfo();

        if (relativeStart == (RESTART_TYPE_DECIDER_UNTIL-1)) {
            RestartType tmp;
            if (conf.fixRestartType == auto_restart)
                tmp = restartTypeChooser->choose();
            else
                tmp = conf.fixRestartType;

            if (tmp == dynamic_restart) {
                glueHistory.fastclear();
                if (conf.verbosity >= 3)
                    std::cout << "c Decided on dynamic restart strategy"
                    << std::endl;
            } else  {
                if (conf.verbosity >= 1)
                    std::cout << "c Decided on static restart strategy"
                    << std::endl;

               // if (!matrixFinder->findMatrixes()) return false; delete by hankf4
			   /**************************************************/
				if ( !matrixFinder->findMatrixes()) // add by hankf4
					return false;
				/**************************************************/
            }
            lastSelectedRestartType = tmp;
            restartType = tmp;
            restartTypeChooser->reset();
        }
    }

    return true;
}

inline void Solver::setDefaultRestartType()
{
    if (conf.fixRestartType != auto_restart) restartType = conf.fixRestartType;
    else restartType = static_restart;

    glueHistory.clear();
    glueHistory.initSize(MIN_GLUE_RESTART);
    conflSizeHist.clear();
    conflSizeHist.initSize(1000);

    lastSelectedRestartType = restartType;
}

/**
@brief The function that brings together almost all CNF-simplifications

It burst-searches for given number of conflicts, then it tries all sorts of
things like variable elimination, subsumption, failed literal probing, etc.
to try to simplifcy the problem at hand.
*/
lbool Solver::simplifyProblem(const uint32_t numConfls)
{
    testAllClauseAttach();
    
    //printf("in simp\n");
	//bool gaussWasCleared = clearGaussMatrixes();  // delete by hankf4
 	const bool EnhancegaussWasCleared = clearEnGaussMatrixes();  //  hankf4 
	
    StateSaver savedState(*this);;

    #ifdef BURST_SEARCH
    if (conf.verbosity >= 3)
        std::cout << "c " << std::setw(24) << " "
        << "Simplifying problem for " << std::setw(8) << numConfls << " confls"
        << std::endl;
    conf.random_var_freq = 1;
    simplifying = true;
    uint64_t origConflicts = conflicts;
    #endif //BURST_SEARCH

    lbool status = l_Undef;

    #ifdef BURST_SEARCH
    restartType = static_restart;

    printRestartStat("S");
    bool oridopure=dopurenow;
    while(status == l_Undef && conflicts-origConflicts < numConfls && needToInterrupt == false) {
	    dopurenow=false;
		//printf("in search\n");
        status = search(100, std::numeric_limits<uint64_t>::max(), false);
		//printf("out of search\n");
    }
	dopurenow=oridopure;
    if (needToInterrupt) return l_Undef;
    printRestartStat("S");
    if (status != l_Undef) goto end;
    #endif //BURST_SEARCH

	///add by alanwang
	if(conf.doXordynamic){
		//printf("in xorfinder2\n");
		XorFinder2 xor_second(this,clauses);
		//printf("out of xorfinder2\n");
		if  (!xor_second.findXors(morexortime)) { 
		//printf("jump to end\n");
		goto end;}
		//else { lockstat=3;}
		//if (conf.doSatELite && !subsumer->simplifyBySubsumption()) goto end;
		}	
	
	////
    if (conf.doXorSubsumption && !xorSubsumer->simplifyBySubsumption()) goto end;

    if (conf.doFailedLit && conf.doCacheOTFSSR) {
        BothCache both(*this);
        if (!both.tryBoth()) goto end;
    }
    if (conf.doCacheOTFSSR) cleanCache();
    if (conf.doClausVivif && !clauseVivifier->vivifyClauses()) goto end;

    if (conf.doCacheOTFSSRSet && order_heap.size() < 200000) {
        if (conf.doCacheOTFSSR == false && conf.verbosity > 0) {
            std::cout << "c turning cache ON because the number of active variables is lower now" << std::endl;
        }
        conf.doCacheOTFSSR = true;
    }
    if (conf.doFailedLit && !failedLitSearcher->search()) goto end;

    if (conf.doSatELite && subsumer && !subsumer->simplifyBySubsumption())
        goto end;

    /*if (findNormalXors && xorclauses.size() > 200 && clauses.size() < MAX_CLAUSENUM_XORFIND/8) {
        XorFinder xorFinder(*this, clauses, ClauseCleaner::clauses);
        if (!xorFinder.doNoPart(3, 7)) {
            status = l_False;
            goto end;
        }
    } else*//* if (xorclauses.size() <= 200 && xorclauses.size() > 0 && nClauses() > 10000) {
        XorFinder x(*this, clauses);
        x.addAllXorAsNorm();
    }*/
    if (xorclauses.size() <= 200+additional_morexor && xorclauses.size() > 0 && nClauses() > 10000) {
        XorFinder x(*this, clauses);
        x.addAllXorAsNorm();
    }
    if (conf.doClausVivif && !clauseVivifier->vivifyClauses()) goto end;

    //addSymmBreakClauses();

    if (conf.doSortWatched) sortWatched();
    if (conf.doCacheOTFSSR &&  conf.doCalcReach) calcReachability();
	
	if(additional_morexor-additional_morexorlast2>0){ 
	additional_morexorlast2=additional_morexor;
	goto end; }

end:
    #ifdef BURST_SEARCH
    if (conf.verbosity >= 3)
        std::cout << "c Simplifying finished" << std::endl;
    #endif //#ifdef BURST_SEARCH

    savedState.restore();
    simplifying = false;

    //if (status == l_Undef && ok && gaussWasCleared && !matrixFinder->findMatrixes())
    //    status = l_False;
    //////////////// add by hanf4 //////////////////////////////
	
    if (status == l_Undef && ok && EnhancegaussWasCleared && !matrixFinder->findMatrixes())
        status = l_False;
	//if (conf.doXorSubsumption && !xorSubsumer->simplifyBySubsumption()) return l_False;
    testAllClauseAttach();

    if (!ok) return l_False;
    return status;
}

/**
@brief Should we perform a full restart?

If so, we also do the things to be done if the full restart is effected.
*/
bool Solver::checkFullRestart(
    uint64_t& nof_conflicts
    , uint64_t& nof_conflicts_fullrestart
    , uint32_t& lastFullRestart
) {
    if (nof_conflicts_fullrestart > 0 && conflicts >= nof_conflicts_fullrestart) {
        #ifdef USE_GAUSS
        //clearGaussMatrixes();  //delete by hankf4
		clearEnGaussMatrixes(); // add by hankf4
        #endif //USE_GAUSS
        //nof_conflicts = conf.restart_first + (double)conf.restart_first*conf.restart_inc;
       // nof_conflicts_fullrestart = (double)nof_conflicts_fullrestart * FULLRESTART_MULTIPLIER_MULTIPLIER;
	   
	   //nof_conflicts = (conf.restart_first + (double)conf.restart_first*conf.restart_inc); // delete by hankf4
		nof_conflicts = (uint64_t)(conf.restart_first + (double)conf.restart_first*conf.restart_inc); // modify by hankf4
        nof_conflicts_fullrestart = (uint64_t)((double)nof_conflicts_fullrestart * FULLRESTART_MULTIPLIER_MULTIPLIER);// modify by hankf4
        restartType = static_restart;
        lastFullRestart = starts;

        if (conf.verbosity >= 3)
            std::cout << "c Fully restarting" << std::endl;
        printRestartStat("F");

        /*if (findNormalXors && clauses.size() < MAX_CLAUSENUM_XORFIND) {
            XorFinder xorFinder(this, clauses, ClauseCleaner::clauses);
            if (!xorFinder.doNoPart(3, 10))
                return false;
        }*/

        //calculateDefaultPolarities();
        if (conf.polarity_mode != polarity_auto) {
            for (uint32_t i = 0; i < polarity.size(); i++) {
                polarity[i] = defaultPolarity();
            }
        }

        fullStarts++;
    }

    return true;
}

/**
@brief Performs a set of pre-optimisations before the beggining of solving

This is somewhat different than the set of optimisations carried out during
solving in simplifyProblem(). For instance, binary xors are searched fully
here, while there, no search for them is carried out. Also, the ordering
is different.

\todo experiment to use simplifyProblem() instead of this, with the only
addition of binary clause search. Maybe it will do just as good (or better).
*/
void Solver::performStepsBeforeSolve()
{
    //assert(qhead == trail.size());
    testAllClauseAttach();

    printRestartStat();
    if (conf.doReplace && !varReplacer->performReplace()) return;

    order_heap.filter(Solver::VarFilter(*this));
    if (order_heap.size() > 300000) {
        if (conf.verbosity > 0) {
            std::cout << "c turning cache OFF because there are too many active variables" << std::endl;
        }
        conf.doCacheOTFSSR = false;
    }

    bool saveDoHyperBin = conf.doHyperBinRes;
    conf.doHyperBinRes = false;
    clauseAllocator.consolidate(this, true);
    if (conf.doFailedLit && !failedLitSearcher->search()) return;
    conf.doHyperBinRes = saveDoHyperBin;
    if (conf.doClausVivif && !conf.libraryUsage
        && !clauseVivifier->vivifyClauses()) return;

    #ifdef VERBOSE_DEBUG
    printAllClauses();
    #endif //VERBOSE_DEBUG
    if (conf.doSatELite
        && !conf.libraryUsage
        && clauses.size() < 4800000
        && subsumer
        && !subsumer->simplifyBySubsumption()
    ) {
        return;
    }

    if (conf.doFindEqLits) {
        if (!sCCFinder->find2LongXors()) return;
        lastNbBin = numNewBin;
        if (conf.doReplace && !varReplacer->performReplace(true)) return;
    }

    if (conf.doFindXors && clauses.size() < MAX_CLAUSENUM_XORFIND) {
        XorFinder xorFinder(*this, clauses);
        if (!xorFinder.fullFindXors(3, 7)) return;
    }

    if (xorclauses.size() > 1) {
        if (conf.doXorSubsumption && !xorSubsumer->simplifyBySubsumption())
            return;

        if (conf.doReplace && !varReplacer->performReplace())
            return;
    }

    if (conf.doSortWatched) sortWatched();
    if (conf.doCacheOTFSSR && conf.doCalcReach) calcReachability();

    testAllClauseAttach();
}

/**
@brief Initialises model, restarts, learnt cluause cleaning, burst-search, etc.
*/
void Solver::initialiseSolver()
{
    //Clear up previous stuff like model, final conflict, matrixes
    model.clear();
    conflict.clear();
   // clearGaussMatrixes();
	// clearGaussMatrixes(); // delete by hankf4
   //printf("initialiseSolver\n"); // add by hankf4
	clearEnGaussMatrixes(); // add by hankf4
    //Initialise restarts & dynamic restart datastructures
    setDefaultRestartType();

    //Initialise avg. branch depth
    avgBranchDepth.clear();
    avgBranchDepth.initSize(500);

    //Initialise number of restarts&full restarts
    starts = 0;
    fullStarts = 0;

    if (conflicts == 0) {
        if (nClauses() * conf.learntsize_factor < nbClBeforeRed) {
            if (nClauses() * conf.learntsize_factor < nbClBeforeRed/2)
                nbClBeforeRed = (uint32_t)(nbClBeforeRed / 4); // modify by hankf4
            else
                nbClBeforeRed = (uint32_t)((nClauses() * conf.learntsize_factor)/2);
        }
    }
     
	 
	 
	 ////
    testAllClauseAttach();
    findAllAttach();
}
/// add by alanwang
void Solver::preproc_pure()
{   
	if(conf.doPureliteral){
			if(litcontain==NULL) litcontain   = new vec<uint32_t> [2*nVars()+2]; 
			
			 
			for(uint32_t x=0; x<(2*nVars()+2 );  x++) { litcontain[x].clear();}
			clauses_cpy.clear(); 
			satby.clear();
			for(uint32_t m=0;m<clauses.size(); m++)
			{  Clause* c = clauses[m];
			   if(c!=NULL&&!(c->getFreed()))
			   {
				
				c->set_cpyindex(clauses_cpy.size());
				clauses_cpy.push(c);
				//assert(!c->get_issat());
				satby.push(lit_Undef.toInt());
				//else
				//{
				// assert()
				//}
				//if(c->size()==3){
				//printf("get size 3\n");
				//}
				//printf("%d \n",c->cpy_index);
			   }
			}
			//if(watch_c.size()==0) {
			watch_c.clear();
			watch_c.growTo(clauses_cpy.size());
			  for(uint32_t k=0;k<clauses_cpy.size();k++)
			  {
			    // vec<uint32_t> kk; kk.push(0);
				// watch_c.push(vec<uint32_t>);
				 watch_c[k].clear();
			  }
			//}
			//if(puresatby==NULL) puresatby = new vec<Lit>      [2*nVars()+2]; 
		   
			 //for(int y=0; y<clauses_cpy.size(); y++)  { watch_c[y].clear();}
			//for(int z=0; z<2*nVars()+2; z++) {puresatby[z].clear();}
			
			//clauseCleaner->cleanClauses(clauses, ClauseCleaner::clauses);
			constructpure=true;
			
			
			for(uint32_t n=0;n<clauses_cpy.size();n++)
			{
				Clause* cc =clauses_cpy[n]; 
				if(cc!=NULL){
				if(!(cc->getFreed())){
						
						for(int m=0; m< cc->size(); m++)
						{
						   uint32_t which= (*cc)[m].toInt();
				
						   if(candopure[(*cc)[m].var()])
						   litcontain[which].push(n);
						}
					}
				}
			}
			
			for(uint32_t m=0;m<2*nVars()+2;m++)
			{
				vec<uint32_t>& temp_m= litcontain[m];
				if(temp_m.size()>0)
				{
				  uint32_t index=temp_m[0]; 
				  watch_c[index].push(m);
				}
				pureseen.push(false);
			}
		}
}
////
/**
@brief The main solve loop that glues everything together

We clear everything needed, pre-simplify the problem, calculate default
polarities, and start the loop. Finally, we either report UNSAT or extend the
found solution with all the intermediary simplifications (e.g. variable
elimination, etc.) and output the solution.
*/
lbool Solver::solve(const vec<Lit>& assumps)
{

     ////for debug alanwan
	 //dopuretime=0;
	 //morexortime=0;
	 //staticStarts_ori=0;
	 //staticStarts_ori_last=0;
	 /////
    assumps.copyTo(assumptions);
    for(size_t i = 0; i < assumptions.size(); i++) {
        Lit& lit = assumptions[i];

        //Update to parent
        lit = varReplacer->getReplaceTable()[lit.var()] ^ lit.sign();
        const Var var = lit.var();

        //Uneliminate
        if (subsumer && subsumer->getVarElimed()[var] && !subsumer->unEliminate(var))
            return l_False;

        if (xorSubsumer->getVarElimed()[var] && !xorSubsumer->unEliminate(var))
            return l_False;
    }

   // #ifdef VERBOSE_DEBUG
   // std::cout << "Solver::solve() called" << std::endl;
   // #endif
   // assert(decisionLevel() == 0);
    if (!ok) return l_False;
    //assert(qhead == trail.size());
    assert(!subsumer || subsumer->checkElimedUnassigned());
    assert(xorSubsumer->checkElimedUnassigned());

    if (libraryCNFFile)
        fprintf(libraryCNFFile, "c Solver::solve() called\n");

    initialiseSolver();
    uint64_t  nof_conflicts = conf.restart_first; //Geometric restart policy, start with this many
    uint64_t  nof_conflicts_fullrestart = conf.restart_first * FULLRESTART_MULTIPLIER + conflicts; //at this point, do a full restart
    uint32_t  lastFullRestart = starts; //last time a full restart was made was at this number of restarts
    lbool     status = l_Undef; //Current status
    uint64_t  nextSimplify = (uint64_t)(conf.restart_first * conf.simpStartMult + conflicts); //Do simplifyProblem() at this number of conflicts
    if (!conf.doSchedSimp) nextSimplify = std::numeric_limits<uint64_t>::max();

    if (conflicts == 0) {
        if (conf.doPerformPreSimp) performStepsBeforeSolve();
        if (!ok) {
            cancelUntil(0);
            return l_False;
        }

        calculateDefaultPolarities();
    }

    printStatHeader();
    printRestartStat("B");
    uint64_t lastConflPrint = conflicts;
	
	/// add by alan wang
	/// initialize pure literal datastructure
	if(clauses.size()>150000){conf.doPureliteral=false;}
	if(conf.doPureliteral){
	clause_trail_lim.clear();
	clause_trail.clear();
	//clause_trail_lim=new uint32_t  [nVars()+1];    for(int x=0;x<nVars()+1;x++) clause_trail_lim[x]=0;
	//clause_trail    =new uint32_t [nClauses()+1];  for(int y=0;y<nClauses()+1;y++) clause_trail[y]=0;
	//clause_trail_sz=0;
	
	//vec<uint32_t>      *  litcontain;
	//vec<uint32_t>      *  watch_c;
	//constructpure=false;
	//litcontain   = new vec<uint32_t> [2*nVars()+2];  
	//watch_c      = new vec<uint32_t> [clauses_cpy.size()+2];
	puresatby 	 = new vec<Lit>      [2*nVars()+2]; 
    preproc_pure();	
	
	}
	/// add by alan wang
	
	
	
    // Search:
    while (status == l_Undef && starts < conf.maxRestarts) {
        #ifdef DEBUG_VARELIM
        assert(!subsumer || subsumer->checkElimedUnassigned());
        assert(xorSubsumer->checkElimedUnassigned());
        #endif //DEBUG_VARELIM

        if ((conflicts - lastConflPrint) > std::min(std::max(conflicts/100*6, (uint64_t)4000), (uint64_t)20000)) {
            printRestartStat("N");
            lastConflPrint = conflicts;
        }

        if (conf.doSchedSimp && conflicts >= nextSimplify) {
            status = simplifyProblem(conf.simpBurstSConf);
            printRestartStat();
            lastConflPrint = conflicts;
            nextSimplify = std::min(
                (uint64_t)((double)conflicts * conf.simpStartMMult)
                , conflicts + MAX_CONFL_BETWEEN_SIMPLIFY
            );
            if (status != l_Undef) break;
        }
		
		if(conf.doPureliteral){
		
		
					if((staticStarts_ori% conf.purefreq)==2&&staticStarts_ori_last!=staticStarts_ori)
					{
						dopurenow=true;
						staticStarts_ori_last=staticStarts_ori;
					}
					
					if(dopuretimes>8&&(dopuretimes%9)==0)
					{
					  conf.purefreq=(uint32_t)((double)conf.purefreq*1.5);
					  if(conf.purefreq>15) conf.purefreq=15;
					}
				}
		

        //status = search(nof_conflicts, std::min(nof_conflicts_fullrestart, nextSimplify));// delete by alanwang
		
		///add by alanwang
		if(!dopurenow){
		
        status = search(nof_conflicts+num_purelearnt, std::min(nof_conflicts_fullrestart+num_purelearnt, nextSimplify));}
		else{
			//clauseCleaner->clearforpurelit();
			//if(first)
			//{
			//	sortWatched();
			//	 //first=false;
			//}
			dopuretimes++;
			uint64_t nof_confpure=(1+(dopuretimes-1)*conf.puresize)*conf.restart_first;
			//printf("%d \n" ,dopuretimes);
			//printf("in search\n");
			status = search( nof_confpure, std::min(nof_conflicts_fullrestart, nextSimplify));
			//printf("out of search \n");
		}
		
		
		if(gauss_learn_size < Gauss_learnts.size() ) {
			gauss_learn_size = Gauss_learnts.size() ;
		}
		
		/////
        if (needToInterrupt) {
            cancelUntil(0);
            return l_Undef;
        }

        //Increment nof_conflicts limit, but only within limits
        if (!dopurenow&&nof_conflicts < 1000L* 1000L*1000L)
           { nof_conflicts = (uint64_t)((double)nof_conflicts * conf.restart_inc);}//modify by hankf4

			
		
		if(dopurenow)
		{
			//dopuretimes++;
			dopurenow=false;
		}
        if (status != l_Undef) break;
        if (!checkFullRestart(nof_conflicts, nof_conflicts_fullrestart , lastFullRestart)) {
            status = l_False;
            break;
        }
        if (!chooseRestartType(lastFullRestart)) {
            status = l_False;
            break;
        }

        if (conf.verbosity>=4) {
            std::cout
            << "c new main loop"
            << " lastFullRestart: " << lastFullRestart
            << " nextSimplify: " << nextSimplify
            << " nof_conflicts_fullrestart: " << nof_conflicts_fullrestart
            << " nof_conflicts: " << nof_conflicts
            << " conflicts: " << conflicts
            << " starts: " << starts
            << std::endl;
        }
    }
    printEndSearchStat();

    #ifdef VERBOSE_DEBUG
    if (status == l_True)
        std::cout << "Solution  is SAT" << std::endl;
    else if (status == l_False)
        std::cout << "Solution is UNSAT" << std::endl;
    else
        std::cout << "Solutions is UNKNOWN" << std::endl;
    #endif //VERBOSE_DEBUG

    if (status == l_True) handleSATSolution();
    else if (status == l_False) handleUNSATSolution();

    cancelUntil(0);
    restartTypeChooser->reset();
    if (status == l_Undef) clauseCleaner->removeAndCleanAll(true);

    #ifdef VERBOSE_DEBUG
    std::cout << "Solver::solve() finished" << std::endl;
    #endif
    return status;
}

/**
@brief Extends a SAT solution to the full solution

variable elimination, variable replacement, sub-part solving, etc. all need to
be handled correctly to arrive at a solution that is a solution to ALL of the
original problem, not just of what remained of it at the end inside this class
(i.e. we need to combine things from the helper classes)
*/
void Solver::handleSATSolution()
{

    /*if (greedyUnbound) {
        double time = cpuTime();
        FindUndef finder(*this);
        const uint32_t unbounded = finder.unRoll();
        if (conf.verbosity >= 1)
            printf("c Greedy unbounding     :%5.2lf s, unbounded: %7d vars\n", cpuTime()-time, unbounded);
    }*/
    assert(!subsumer || subsumer->checkElimedUnassigned());
    assert(xorSubsumer->checkElimedUnassigned());

    varReplacer->extendModelPossible();
    checkSolution();

    if ((subsumer && subsumer->getNumElimed()) || xorSubsumer->getNumElimed()) {
        if (conf.verbosity >= 1) {
            std::cout << "c Solution needs extension. Extending." << std::endl;
        }
        Solver s;
        s.conf = conf;
        s.conf.doSatELite = false;
        s.conf.doReplace = false;
        s.conf.doFindEqLits = false;
        s.conf.doRegFindEqLits = false;
        s.conf.doFailedLit= false;
        s.conf.doConglXors = false;
        s.conf.doSubsWNonExistBins = false;
        s.conf.doRemUselessBins = false;
        s.conf.doClausVivif = false;
        s.conf.doSortWatched = false;
        s.conf.verbosity = 0;

        vec<Lit> tmp;
        for (Var var = 0; var < nVars(); var++) {
            s.newVar(decision_var[var]
            || (subsumer && subsumer->getVarElimed()[var])
            || varReplacer->varHasBeenReplaced(var)
            || xorSubsumer->getVarElimed()[var]
            );

            //assert(!(xorSubsumer->getVarElimed()[var] && (decision_var[var] || subsumer->getVarElimed()[var] || varReplacer->varHasBeenReplaced(var))));

            if (value(var) != l_Undef) {
                #ifdef VERBOSE_DEBUG
                std::cout << "Setting var " << var + 1
                << " in extend-solver to " << value(var) << std::endl;
                #endif
                tmp.clear();
                tmp.push(Lit(var, value(var) == l_False));
                s.addClause(tmp);
            }
        }
        varReplacer->extendModelImpossible(s);

        if (subsumer)
            subsumer->extendModel(s);

        xorSubsumer->extendModel(s);

        lbool status = s.solve();
        release_assert(status == l_True && "c ERROR! Extension of model failed!");
#ifdef VERBOSE_DEBUG
        std::cout << "Solution extending finished. Enqueuing results" << std::endl;
#endif
        //need to start new decision level, otherwise uncheckedEnqueue will
        //enqueue to decision level 0 in certain cases :S
        newDecisionLevel();
        for (Var var = 0; var < nVars(); var++) {
            if (assigns[var] == l_Undef && s.model[var] != l_Undef)
                uncheckedEnqueue(Lit(var, s.model[var] == l_False));
        }
        ok = (propagate<false>().isNULL());
        release_assert(ok && "c ERROR! Extension of model failed!");
    }
    checkSolution();
    //Copy model:
    model.growTo(nVars());
    for (Var var = 0; var != nVars(); var++) model[var] = value(var);
}

/**
@brief When problem is decided to be UNSAT, this is called

There is basically nothing to be handled for the moment, but this could be
made extensible
*/
void Solver::handleUNSATSolution()
{
    if (conflict.size() == 0)
        ok = false;
}

void Solver::cleanCache()
{
    for(uint32_t i = 0; i < nVars(); i++) {
        if ((subsumer && subsumer->getVarElimed()[i])
            || value(i) != l_Undef
        ) {
            vector<Lit> tmp1;
            transOTFCache[Lit(i, false).toInt()].lits.swap(tmp1);
            vector<Lit> tmp2;
            transOTFCache[Lit(i, true).toInt()].lits.swap(tmp2);
            continue;
        }

        for(int which = 0; which < 2; which++) {
            cleanCachePart(Lit(i, which));

        }
    }
}

void Solver::cleanCachePart(const Lit vertLit)
{
    vector<Lit>& transCache = transOTFCache[(~vertLit).toInt()].lits;
    //assert(seen_vec.empty());

    vector<Lit>::iterator it = transCache.begin();
    vector<Lit>::iterator it2 = it;

    size_t newSize = 0;
    for (vector<Lit>::iterator end = transCache.end(); it != end; it++) {
        Lit lit = *it;
        lit = varReplacer->getReplaceTable()[lit.var()] ^ lit.sign();
        if (lit == vertLit
            || seen[lit.toInt()]
            || (subsumer && subsumer->getVarElimed()[lit.var()])
            || (subsumer && subsumer->getVarElimed()[lit.var()])
        ) continue;

        *it2++ = lit;

        //Don't allow the same value to be in the cache twice
        seen[lit.toInt()] = 1;
        seen_vec.push_back(lit);

        //Increase valid size
        newSize++;
    }
    transCache.resize(newSize);

    //Clear up seen
    for(vector<Lit>::const_iterator it = seen_vec.begin(), end = seen_vec.end(); it != end; it++) {
        seen[it->toInt()] = 0;
    }
    seen_vec.clear();
}

const vector<pair<Lit, Lit> > Solver::get_all_binary_xors() const
{
    vector<pair<Lit, Lit> > ret;

    const vector<Lit>& table = varReplacer->getReplaceTable();
    for (Var var = 0; var != table.size(); var++) {
        Lit lit = table[var];
        if (lit.var() == var)
            continue;

        ret.push_back(std::make_pair(Lit(var, false), lit));
    }

    return ret;
}

void Solver::resetPolaritiesToRand()
{
    for(vector<char>::iterator it = polarity.begin(), end = polarity.end(); it != end; it++)
        *it = mtrand.randInt(1);
}

void Solver::addAllXorAsNorm()
{
    //assert(ok);
    XorFinder xorFinder(*this, clauses);
    xorFinder.addAllXorAsNorm();
}
