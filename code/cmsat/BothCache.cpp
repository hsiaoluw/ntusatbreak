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

#include "cmsat/BothCache.h"
#include "cmsat/time_mem.h"
#include <iomanip>
#include "cmsat/VarReplacer.h"
#include "cmsat/Subsumer.h"
#include "cmsat/XorSubsumer.h"
//#include "xorfinder2.h"
//#include "cmsat/Solver.h"
//#include "simplifier.h"
#include "cmsat/Clause.h"
#include <limits>
namespace CMSat {
using std::cout;
using std::endl;

BothCache::BothCache(Solver& _solver) :
    solver(_solver)
{}

bool BothCache::tryBoth()
{
    vec<bool> seen(solver.nVars(), 0);
    vec<bool> val(solver.nVars(), 0);
    vec<Lit> tmp;
    uint32_t bProp = 0;
    uint32_t bXProp = 0;
    double myTime = cpuTime();
    uint32_t backupTrailSize = solver.trail.size();

    for (Var var = 0; var < solver.nVars(); var++) {
        if (solver.value(var) != l_Undef
            || (solver.subsumer && solver.subsumer->getVarElimed()[var])
            || solver.xorSubsumer->getVarElimed()[var]
            || solver.varReplacer->getReplaceTable()[var].var() != var)
            continue;

        Lit lit = Lit(var, false);
        vector<Lit> const* cache1;
        vector<Lit> const* cache2;

        bool startWithTrue;
        if (solver.transOTFCache[lit.toInt()].lits.size() < solver.transOTFCache[(~lit).toInt()].lits.size()) {
            cache1 = &solver.transOTFCache[lit.toInt()].lits;
            cache2 = &solver.transOTFCache[(~lit).toInt()].lits;
            startWithTrue = false;
        } else {
            cache1 = &solver.transOTFCache[(~lit).toInt()].lits;
            cache2 = &solver.transOTFCache[lit.toInt()].lits;
            startWithTrue = true;
        }

        if (cache1->size() == 0) continue;

        for (vector<Lit>::const_iterator it = cache1->begin(), end = cache1->end(); it != end; it++) {
            seen[it->var()] = true;
            val[it->var()] = it->sign();
        }

        for (vector<Lit>::const_iterator it = cache2->begin(), end = cache2->end(); it != end; it++) {
            if (seen[it->var()]) {
                Var var2 = it->var();
                if ((solver.subsumer && solver.subsumer->getVarElimed()[var2])
                    || solver.xorSubsumer->getVarElimed()[var2]
                    || solver.varReplacer->getReplaceTable()[var2].var() != var2)
                    continue;

                if  (val[it->var()] == it->sign()) {
                    tmp.clear();
                    tmp.push(*it);
                    solver.addClauseInt(tmp, true);
                    if  (!solver.ok) goto end;
                    bProp++;
                } else {
                    tmp.clear();
                    tmp.push(Lit(var, false));
                    tmp.push(Lit(it->var(), false));
                    bool sign = true ^ startWithTrue ^ it->sign();
                    solver.addXorClauseInt(tmp, sign);
                    if  (!solver.ok) goto end;
                    bXProp++;
                }
            }
        }

        for (vector<Lit>::const_iterator it = cache1->begin(), end = cache1->end(); it != end; it++) {
            seen[it->var()] = false;
        }
    }

    end:
    if (solver.conf.verbosity >= 1) {
        std::cout << "c Cache " <<
        " BProp: " << bProp <<
        " Set: " << (solver.trail.size() - backupTrailSize) <<
        " BXProp: " << bXProp <<
        " T: " << (cpuTime() - myTime) <<
        std::endl;
    }

    return solver.ok;
}
XorFinder2::XorFinder2(Solver* _solver ,vec<Clause*>& _cls) :
    
     solver(_solver)
    , numCalls(0)
    , cls(_cls)
{
    seen.clear();
    for(int k=0;k<(_solver)->nVars();k++){
	
	  seen.push_back(0);
	 // seen.push_back(0); 
	}
}

bool XorFinder2::findXors(double& totaltime)
{   
    //printf("in findxors\n");
    maxTimeFindXors = 200LL*1000LL*1000LL;
    double myTime = cpuTime();
	if(myTime>700.0) return true;//
	if(totaltime>10.0){
	if((myTime/totaltime)<25.0&&myTime>60.0) return true;}
    numCalls++;
    runStats.clear();
    xors.clear();
    xorOcc.clear();
    xorOcc.resize(solver->nVars());
    triedAlready.clear();

    vec<Lit> lits;
    for (Clause** 
        it = cls.getData()
        , **end = cls.getDataEnd()
        ; it != end //&& maxTimeFindXors > 0
        ; it++
    ) {
        
         Clause* cl = (* it);
        //maxTimeFindXors -= 3;

        //Already freed
        if (cl->getFreed())
            continue;

        //Too large -> too expensive
        //if (cl->size() > solver->conf.maxXorToFind)
		if (cl->size() > 4||cl->size()<2)
            //return solver->ok;
			continue;

		const ClauseOffset offset=solver->clauseAllocator.getOffset(cl);	 
        //If not tried already, find an XOR with it
		if(solver->getinfoAlready.find(offset)!=solver->getinfoAlready.end()){ continue; }
		else {offset_wait.clear();}
		solver->findxor=false;
        if (triedAlready.find(offset) == triedAlready.end()) {
            triedAlready.insert(offset);

            lits.growTo(cl->size());
            for(size_t i = 0; i < cl->size(); i++) {
                lits[i] = (*cl)[i];
            }
            findXor(lits, cl->getabst());
			
			if(solver->findxor)
			{
			
			   solver->getinfoAlready.insert(offset);
			   if(offset_wait.size()>0){
			   for(uint32_t u=0;u<offset_wait.size();u++)
			       solver->getinfoAlready.insert(offset_wait[u]);
				  }
			}
			
			if(!solver->ok) {
			//printf("c Finding howmany  XORs ?:    %7d \n", xors.size());
			solver->additional_xor+=xors.size();
			return solver->ok;}
        }
		
		
    }

    size_t wsLit = 0;
    for (vec<vec<Watched> >::const_iterator
        it = solver->watches.begin(), end = solver->watches.end()
        ; it != end //&& maxTimeFindXors > 0
        ; it++, wsLit++
    ) {
        const Lit lit = Lit::toLit(wsLit);
        const vec<Watched>& ws = *it;

        //maxTimeFindXors -= ws.size()*3;
        for (vec<Watched>::const_iterator
            it2 = ws.begin(), end2 = ws.end()
            ; it2 != end2
            ; it2++
        ) {
            //Only care about tertiaries
			 
        //If not tried already, find an XOR with it
            
            if (!it2->isTriClause())
                continue;

			
            //Only bother about each tri-clause once
			
			
            if (lit > (it2->getOtherLit())
                || ((it2->getOtherLit()) > (it2->getOtherLit2()) )
            ) {
                continue;
            }

            lits.growTo(3);
            lits[0] = lit;
            lits[1] = it2->getOtherLit();
            lits[2] = it2->getOtherLit2();

            findXor(lits, calcAbstraction(lits));
			if(!solver->ok) {
			//printf("c Finding howmany  XORs ?:    %7d \n", xors.size());
			
			solver->additional_xor+=xors.size();
			return solver->ok;}
        }
    }


    //Calculate & display stats
    runStats.findTime = cpuTime() - myTime;
	totaltime+=cpuTime()-myTime;
    assert(runStats.foundXors == xors.size());
     /*
    if (solver->conf.verbosity >= 5) {
        cout << "c Found XORs: " << endl;
        for(vec<Xor2>::iterator
            it = xors.begin(), end = xors.end()
            ; it != end
            ; it++
        ) {
            cout << "c " << *it << endl;
        }
    }*/
    /* 
    if (solver->conf.doEchelonizeXOR && xors.size() > 0) {
        extractInfo();
    }
     */
   // if (solver->conf.verbosity >= 1) {
   //     runStats.printShort();
   // }

    globalStats += runStats;
	//if(!solver->ok) {
			//printf("c Finding howmany  XORs ?:    %7d \n", xors.size());}
    //printf("c Finding howmany  XORs ?:    %7d \n", xors.size());
	solver->additional_xor+=xors.size();
    return solver->ok;
}

void XorFinder2::findXor(vec<Lit>& litss, CL_ABST_TYPE abst)
{
    //printf("in findxor\n");
    //Set this clause as the base for the FoundXors
    //fill 'seen' with variables
	std::sort(litss.begin(), litss.end());
    FoundXors foundCls(litss, abst, seen);
    needprint=false;
    //Try to match on all literals
    for (vec<Lit>::const_iterator
        l = litss.begin(), end = litss.end()
        ; l != end
        ; l++
    ) {
	
	     if(     //
		 
		 
				   solver->value((*l).var()) != l_Undef
		       ||   solver->varReplacer->getReplaceTable()[(*l).var()].var() != (*l).var()
               //||  solver->partHandler->getSavedState()[(*l).var()] != l_Undef
		       ||  (solver->subsumer&&solver->subsumer->getVarElimed()[(*l).var()]   )    
               ||  solver->xorSubsumer->getVarElimed()[(*l).var()]
           )
			continue;
	
        findXorMatch(solver->transOTFCache[(*l).toInt()].lits, (*l), foundCls);
        findXorMatch(solver->transOTFCache[(~(*l)).toInt()].lits, ~(*l), foundCls);

		findXorMatch(solver->watches[(*l).toInt()], *l, foundCls);
        findXorMatch(solver->watches[(~(*l)).toInt()], ~(*l), foundCls);
        //More expensive
        //findXorMatchExt(solver->watches[(*l).toInt()], *l, foundCls);
        //findXorMatchExt(solver->watches[(~(*l)).toInt()], ~(*l), foundCls);

        //TODO stamping
        /*if (solver->conf.useCacheWhenFindingXors) {
            findXorMatch(solver->implCache[(*l).toInt()].lits, *l, foundCls);
            findXorMatch(solver->implCache[(~*l).toInt()].lits, ~(*l), foundCls);
        }*/

        //maxTimeFindXors -= 5;
        if (foundCls.foundAll())
            break;
    }

    //maxTimeFindXors -= 5;
    if (foundCls.foundAll()) {
        Xor2 thisXor(litss, foundCls.getRHS());
        assert(xorOcc.size() > litss[0].var());
        #ifdef VERBOSE_DEBUG_XOR_FINDER
        cout << "XOR found: " << litss << endl;
        #endif

        //Have we found this XOR clause already?
        const vector<uint32_t>& whereToFind = xorOcc[litss[0].var()];
        bool found = false;
        for (vector<uint32_t>::const_iterator
            it = whereToFind.begin(), end = whereToFind.end()
            ; it != end
            ; it++
        ) {
            if (xors[*it] == thisXor) {
                found = true;
                break;
            }
        }

        //If XOR clause is new, add it
        if (!found) {
			foundCls.getmoreXorinfo(solver);
			//if(litss.size()>2) goto end;
		    if(solver->addXorClause(litss, foundCls.getRHS())) 
			{
				//maxTimeFindXors -= 20;
				xors.push_back(thisXor);
				if(litss.size()>2) {solver->additional_morexor++;}
				solver->findxor=true;
				runStats.foundXors++;
				runStats.sumSizeXors += litss.size();
				uint32_t thisXorIndex = xors.size()-1;
				
				
				
				for (vec<Lit>::const_iterator
					l = litss.begin(), end = litss.end()
					; l != end
					; l++
				) {
					xorOcc[l->var()].push_back(thisXorIndex);
					//printf("%d ", l->var());
				}
				//printf("\n");
				//needprint=true;
				//foundCls.getmoreXorinfo(solver);
			}	 
			 
				//if (!solver->ok) return;
            
        }
		goto end;
    }

	else 
	{
	  foundCls.getmoreXorinfo(solver);
	
	  goto end;
	}
    //Clear 'seen'
   /* for (vec<Lit>::const_iterator
        l = litss.begin(), end = litss.end()
        ; l != end
        ; l++
    ) {
        seen[(*l).var()] = 0;
		
    }*/
	end:
	for(size_t i = 0; i < foundCls.getSize(); i++) {
                seen[foundCls.origCl[i].var()]=0;
			 //if(needprint)	printf("%d " , foundCls.origCl[i].var());
            }
			//if(needprint) printf("\n nVars=%d \n", solver->nVars());
	//printf("out of findxor\n");
}





void XorFinder2::findXorMatch(
    const vec<Watched>& occ
    , const Lit lit
    , FoundXors& foundCls
) {
   // printf("in findxormatch 1\n");
    //maxTimeFindXors -= occ.size();
    for (vec<Watched>::const_iterator
        it = occ.begin(), end = occ.end()
        ; it != end
        ; it++
    ) {
	
	   
        //Deal with binary
        if (it->isBinary()) {
            if (//Only once per binary
                lit < it->getOtherLit()
                //only for correct binary
				//&& solver->value((it->getOtherLit()).var()) == l_Undef
                && seen[it->getOtherLit().var()]
			    && solver->varReplacer->getReplaceTable()[(it->getOtherLit()).var()].var() == it->getOtherLit().var()
                //&& solver->partHandler->getSavedState()[(it->getOtherLit()).var()] == l_Undef
		        &&(!solver->subsumer||!solver->subsumer->getVarElimed()[(it->getOtherLit()).var()])       
                &&(!solver->xorSubsumer->getVarElimed()[(it->getOtherLit()).var()])
           )
             {
			    /*printf("in double, v1=%d , v2=%d \n", lit.var(), it->getOtherLit().var());
				for(int i=0;i<foundCls.getSize();i++ )
				{
				  printf(" %d", foundCls.origCl[i].var());
				}
				printf("\n");
				for(int j=0;j<seen.size();j++)
				{
				 if (seen[j]) printf(" %d", j);
				}
				printf("\n");*/
                tmpClause.clear();
                tmpClause.push(~lit);
                tmpClause.push((it->getOtherLit()));
                std::sort(tmpClause.begin(), tmpClause.end());
				//printf("in wat ");
                foundCls.add(tmpClause, varsMissing);
                //maxTimeFindXors-=5;
                if (foundCls.foundAll())
                    break;
            }

            continue;
        }
        
        //Deal with tertiary
        if (it->isTriClause()) {
		    
            if (//Only once per tri
                lit < it->getOtherLit() && it->getOtherLit() < it->getOtherLit2()

                //Only for correct tri
                && seen[it->getOtherLit().var()] && seen[it->getOtherLit2().var()]
				&& solver->varReplacer->getReplaceTable()[(it->getOtherLit()).var()].var() == it->getOtherLit().var()
                //&& solver->partHandler->getSavedState()[(it->getOtherLit()).var()] == l_Undef
		        &&(!solver->subsumer||(!solver->subsumer->getVarElimed()[(it->getOtherLit()).var()]) )      
                &&(!solver->xorSubsumer->getVarElimed()[(it->getOtherLit()).var()])
				&& solver->varReplacer->getReplaceTable()[(it->getOtherLit2()).var()].var() == it->getOtherLit2().var()
                //&& solver->partHandler->getSavedState()[(it->getOtherLit2()).var()] == l_Undef
		        &&(!solver->subsumer||(!solver->subsumer->getVarElimed()[(it->getOtherLit2()).var()])   )    
                &&(!solver->xorSubsumer->getVarElimed()[(it->getOtherLit2()).var()])
            ) {
			    //printf("in tri\n");
                bool rhs = true;
                rhs ^= !(lit.sign());
                rhs ^= (it->getOtherLit().sign());
                rhs ^= (it->getOtherLit2().sign());

                
                    tmpClause.clear();
                    tmpClause.push(~lit);
                    tmpClause.push((it->getOtherLit()));
                    tmpClause.push((it->getOtherLit2()));
                    std::sort(tmpClause.begin(), tmpClause.end());
                    foundCls.add(tmpClause, varsMissing);
                    //maxTimeFindXors-=5;
                    if (foundCls.foundAll())
                        break;
                

            }
            continue;
        }
        
        //Deal with clause
		if(((it->data2)&3)== 2) continue;
        const ClauseOffset offset = it->getNormOffset();
         Clause * cl = solver->clauseAllocator.getPointer(offset);
        if (cl->getFreed())
            continue;

        //Must not be larger than the original clause
        if (cl->size() > foundCls.getSize())
            continue;

        //Doesn't contain literals not in the original clause
       //Doesn't contain literals not in the original clause
        if ((cl->getabst() | foundCls.getAbst()) != foundCls.getAbst())
            continue;

        //Check RHS
        bool rhs = true;
        for (const Lit
            *l = cl->begin(), *end = cl->end()
            ; l != end
            ; l++
        ) {
            //early-abort, contains literals not in original clause
            if (!seen[l->var()]
			 || solver->varReplacer->getReplaceTable()[l->var()].var() != l->var()
            // || solver->partHandler->getSavedState()[l->var()] != l_Undef
		     ||(solver->subsumer&&solver->subsumer->getVarElimed()[l->var()])       
             ||(solver->xorSubsumer->getVarElimed()[l->var()])
			
			)
                goto end;

            rhs ^= l->sign();
        }
        //either the invertedness has to match, or the size must be smaller
       // if (rhs != foundCls.getRHS() && cl->size() == foundCls.getSize())
       //     continue;

        //If the size of this clause is the same of the base clause, then
        //there is no point in using this clause as a base for another XOR
        //because exactly the same things will be found.
        if (cl->size() == foundCls.getSize())
           { triedAlready.insert(offset);
		     offset_wait.push_back(offset);
		   }
        tmpClause.clear();
        for(int i=0;i<cl->size();i++)
		{
		 tmpClause.push((*cl)[i]);
		}
		//printf("in more\n");
		std::sort(tmpClause.begin(), tmpClause.end());
        foundCls.add(tmpClause, varsMissing);
        //maxTimeFindXors-=5;
        if (foundCls.foundAll())
            break;
        
        end:;
    }
	//printf("end findxormatch 1\n");
}



void XorFinder2::findXorMatch(
    
	const vector<Lit>& occ
    , const Lit lit
    , FoundXors& foundCls
) {//printf("in findxormatch 2\n");
   //printf("occ.size()=%d\n", occ.size());
    //maxTimeFindXors -= occ.size();
    for (vector<Lit>::const_iterator
        it = occ.begin(), end = occ.end()
        ; it != end
        ; it++
    ) {
	
		        Var var2 = it->var();
                if (   //solver->value(var2) != l_Undef	
					   (solver->subsumer&&solver->subsumer->getVarElimed()[var2])
                    || solver->xorSubsumer->getVarElimed()[var2]
                    || solver->varReplacer->getReplaceTable()[var2].var() != var2)
                  //  || solver->partHandler->getSavedState()[var2] != l_Undef)
                    continue;
	
        //Deal with binary
       
				  //printf("var: %d  \n", (int)(*it).var());
				if (
				
					seen[(*it).var()]&& lit.var() !=(*it).var()
				) {
					tmpClause.clear();
					tmpClause.push(lit);
					tmpClause.push((*it));
                    std::sort(tmpClause.begin(), tmpClause.end());
					foundCls.add(tmpClause, varsMissing);
					//maxTimeFindXors-=5;
					if (foundCls.foundAll())
						break;
				}
            
            //continue;
        }
	//printf("end findxormatch 2\n");
}

uint64_t XorFinder2::memUsed() const
{//printf("in memUsed\n");
    uint64_t mem = 0;
    mem += xors.capacity()*sizeof(Xor2);
    mem += xorOcc.capacity()*sizeof(vec<uint32_t>);
    for(size_t i = 0; i < xorOcc.size(); i++) {
        mem += xorOcc[i].capacity()*sizeof(uint32_t);
    }
    mem += triedAlready.size()*sizeof(ClauseOffset); //TODO very much under-estimates
    mem += blocks.capacity()*sizeof(vec<Var>);
    for(size_t i = 0; i< blocks.size(); i++) {
        mem += blocks[i].capacity()*sizeof(Var);
    }
    mem += varToBlock.capacity()*sizeof(size_t);
    vec<size_t> varToBlock; ///<variable-> block index map

    //Temporary
    //mem += tmpClause.capacity()*sizeof(Lit);
    mem += varsMissing.capacity()*sizeof(uint32_t);

    //Temporaries for putting xors into matrix, and extracting info from matrix
    mem += outerToInterVarMap.capacity()*sizeof(size_t);
    mem += interToOUterVarMap.capacity()*sizeof(size_t);
//printf("end memused\n");
    return mem;
}

bool  FoundXors::getmoreXorinfo(Solver* solver)
{    //printf("in getmore\n");
     uint32_t half= (1<<(size-1)) ;
	 checklist_s.clear();
     checklist_v.clear();
	 if(even_list.size()==half&&odd_list.size()==half)
	 {return false;}
	 if(even_list.size()==0||odd_list.size()==0)
	 {return true;}
	 
	 
    //only one solution 
    if((even_list.size()+odd_list.size())==foundComb.size()-1)
    {   assert(even_list.size()==half|| odd_list.size()==half);
	    uint32_t whichone=0;
	    for(uint32_t i = 0; i < foundComb.size(); i++)
	       {if(!foundComb[i]) whichone=i ; break;}
		   
		vec<Lit>  tmp_l;  
        for(uint32_t j=0;j<size ;j++)
        {
		    bool ss= bit(whichone,j);
		    
			tmp_l.clear();
			tmp_l.push(Lit( origCl[j].var(), !ss));
			//if(solver->value(origCl[j].var()) == l_Undef)
		    //{
			 //printf("imply by lack-1 %d%d\n", origCl[j].var(),!ss);
			 solver->addLearntClause(tmp_l);
			 solver->additional_three++;
			
			//}
			   if  (!solver->ok)
					 { //printf("not-ok-631\n");
					  return solver->ok; } 
		} 		
	}
	//subsumer would help us do this
	
	else if(size>3&&(even_list.size()<4||odd_list.size()<4))
	{return true;}
	
	else if(size==3&&(even_list.size()<2||odd_list.size()<2))
	{return true;}
	
    else if(size==3){
	      checklist_s.clear();
		  checklist_v.clear();
	      for(uint32_t k=0;k<even_list.size();k++)
		  {
				for(uint32_t l=0;l<odd_list.size();l++)
				{
					uint32_t compare_num=0 , lower=0;
					if(even_list[k]> odd_list[l])
					{compare_num=even_list[k]^odd_list[l]; lower=odd_list[l];}
					else
					{compare_num=odd_list[l]^even_list[k]; lower=even_list[k];}
					
					
					//if(compare_num<0) {compare_num=0- compare_num;  lower=even_list[k];       }
					//bool findcompare=false;
					for(uint j=0;j<size;j++)
					{   if(compare_num==(1UL<<j))
						{
						   uint32_t mask2 = compare_num-1 ; /// 00011
						   uint32_t mask1 =  (1UL<<size)-1-mask2-compare_num; /// 11100
						   
						   //printf("%d %d\n", mask1, mask2);
						   //assert(mask1>mask2);
						   
						   uint32_t value = ( (1UL<<(size))-(1UL+compare_num));
						   uint32_t sign_v = ((lower&mask1)>>1)+(lower&mask2);
						   //printf("%d , %d\n",even_list[k],odd_list[l]);
						   //assert((((even_list[k]&mask1)>>1)+(even_list[k]&mask2))==(((odd_list[l]&mask1)>>1)+(odd_list[l]&mask2)));
						   //assert(((lower&mask1)>>1)>(lower&mask2));
						   vector<uint32_t> newv; newv.clear();
						   
						   bool findsame=false;
						   for(uint32_t i=0;i<checklist_v.size();i++)
						   {
							   if(checklist_v[i]==value)
								   {findsame=true;
									vector<uint32_t>& tmp =checklist_s[i];
									tmp.push_back(sign_v);
									break;
								   }
						   }
						   
						   if(!findsame)
						   {
							  checklist_v.push_back(value);
							  newv.push_back(sign_v);
							  checklist_s.push_back(newv);
						   }
						   //findcompare=true;
						   break;
						}
					
					}
					//assert(findcompare);
				}
		  }
	}
	// check for equivalence , implication
	//vector<vector<uint32>> list; 
	
	else if(size==4)
	{
	      even_list_four.clear();
		  odd_list_four.clear();
		  checklist_s.clear();
		  checklist_v.clear();
	      for(uint32_t k=0;k<even_list.size();k++)
		  {
				for(uint32_t l=0;l<odd_list.size();l++)
				{
					uint32_t compare_num=0 , lower=0;
					if(even_list[k]> odd_list[l])
					{compare_num=even_list[k]^odd_list[l]; lower=odd_list[l];}
					else
					{compare_num=odd_list[l]^even_list[k]; lower=even_list[k];}
					
					
					//if(compare_num<0) {compare_num=0- compare_num;  lower=even_list[k];       }
					//bool findcompare=false;
					for(uint j=0;j<size;j++)
					{   if(compare_num==(1UL<<j))
						{
						   uint32_t mask2 = compare_num-1 ; /// 00011
						   uint32_t mask1 =  (1UL<<size)-1-mask2-compare_num; /// 11100
						   
						   //printf("%d %d\n", mask1, mask2);
						   //assert(mask1>mask2);
						   
						   uint32_t value = ( (1UL<<(size))-(1UL+compare_num));
						   
						   assert((value&odd_list[l])==(value&even_list[k]));
						   
						   if(lower==even_list[k])
						   even_list_four.push_back((value<<size)+(value&even_list[k]));
						   else
						   odd_list_four.push_back((value<<size)+(value&odd_list[l]));
						   
						}
					}
					//assert(findcompare);
				}
		  }
		  
		//handle 3  
		for(uint32_t k=0;k<even_list_four.size();k++)
		  {
				for(uint32_t l=0;l<odd_list_four.size();l++)
				{
					uint32_t compare_num=0 , lower=0;
					uint32_t value_e    =(even_list_four[k]>>size);
					uint32_t value_o    =(odd_list_four[l]>>size);
					if(value_e==value_o){
					uint32_t sign_e     =(even_list_four[k]&&((1UL<<size)-1));
					uint32_t sign_o 	=(odd_list_four[l]&&((1UL<<size)-1));
					compare_num=sign_e^sign_o;
					
					//if(compare_num<0) {compare_num=0- compare_num;  lower=even_list[k];       }
					//bool findcompare=false;
					for(uint j=0;j<size;j++)
					{   if(compare_num==(1UL<<j))
						{
						  
						   //printf("%d %d\n", mask1, mask2);
						   //assert(mask1>mask2);
						   
						   uint32_t value = (value_e&value_o)- compare_num;
						   //printf("value=%d\n", value);
						   //assert(value==3||value==5||value==9||value==6||value==10||value==12);
						   uint32_t sign_v =0;
                            uint32_t k=0; 
						   for(uint32_t m=0;m<size;m++)
						   {
						      
						      if((value>>m)&1)
						         {
								     sign_v+=((sign_e>>m)&1)<<k;
								      k++;
									  assert(((sign_e>>m)&1)==((sign_o>>m)&1));
								 }
						   }
						   
						   assert(k==1);
						  
						   vector<uint32_t> newv; newv.clear();
						   
						   bool findsame=false;
						   for(uint32_t i=0;i<checklist_v.size();i++)
						   {
							   if(checklist_v[i]==value)
								   {findsame=true;
									vector<uint32_t>& tmp =checklist_s[i];
									tmp.push_back(sign_v);
									break;
								   }
						   }
						   
						   if(!findsame)
						   {
							  checklist_v.push_back(value);
							  newv.push_back(sign_v);
							  checklist_s.push_back(newv);
						   }
						   //findcompare=true;
						   break;
						}
					
					}
				  }
					//assert(findcompare);
				}
		  }  
	}
	
	
	
	else {return true;}
	
	if(checklist_s.size()>0){
		for (uint32_t i=0 ;i<checklist_s.size();i++)
		{
			 vector<uint32_t>& now =checklist_s[i];
			 //printf("now=%d\n",now.size());
			 assert(now.size()<4);
			 vec<Var> thetwo_var; thetwo_var.clear();
			 vec<Lit> tmp_l ;     tmp_l.clear();
			 for(uint32_t  j=0;j<size;j++){
			 
			 if(bit(checklist_v[i],j))
			 thetwo_var.push(origCl[j].var());
			 }
			 
			 //assert(thetwo_var.size()==2 && "the two var must equal to two");
			 
			
				if(now.size()==3)  // the sign of the two var have been decided
				{
				   // find which one is lack 0+1+2+3=6
				   uint32_t the_lack=0;
				   uint32_t total=0;
				   for(uint32_t m=0;m<3; m++)
					 { 
					   total+=now[m]; 
					   //printf("now[%d]=%d\n", m, now[m]);
					 }
					 the_lack=7-total;
					 //printf("the lack %d\n", the_lack);
					 assert(the_lack<5&&the_lack>0);
					 the_lack--;
					 //printf("the lack:%d\n", the_lack);
					 tmp_l.clear();
					 tmp_l.push(Lit(thetwo_var[0],!(the_lack&1)));
					 //printf("the unit-c=%d%d\n",thetwo_var[0],!(the_lack&1)  );

					// if(solver->value(thetwo_var[0]) == l_Undef)
					 //{
						solver->addLearntClause(tmp_l);
					    solver->additional_three++;
					 
					 //}
						if  (!solver->ok)
					 { //printf("not-ok-716\n");
					  return solver->ok; }    
					 
					 tmp_l.clear();
					 tmp_l.push(Lit(thetwo_var[1],!((bool)((the_lack>>1)&1))));
					 //printf("the unit-c=%d%d\n",thetwo_var[1],!((the_lack>>1)&1)   );
				
					 //if(solver->value(thetwo_var[1]) == l_Undef)
					 //{
					 solver->addLearntClause(tmp_l);
					 solver->additional_three++;
					 solver->findxor=true;
					 //}
							 if  (!solver->ok)
						 { //printf("not-ok-723\n");
						  return solver->ok; } 
				}
				// 2-xor or assign an value
				else if(now.size()==2)
				{
				 
				 bool rhs_f=true^(!((bool)(now[0]&1)))^((bool)((now[0]>>1)&1));
				 bool rhs_s=true^(!((bool)(now[1]&1)))^((bool)((now[1]>>1)&1));
				  if(rhs_f==rhs_s){
					bool rhs_l=true^(!((bool)(now[0]&1)))^((bool)(now[0]>>1&1));    
						 tmp_l.clear();
						 tmp_l.push(Lit(thetwo_var[0], false));
						 tmp_l.push(Lit(thetwo_var[1], false));
						 /*printf("--------------------------------------------------------------------orig:");
				         for(uint32_t x=0;x<size;x++)
						{printf("%d%d ",origCl[x].var(),origCl[x].sign()); }
						printf("\n");
						 printf("the---------------xor:%d%d %d%d\n",tmp_l[0].var(),tmp_l[0].sign(), tmp_l[1].var(), tmp_l[1].sign() );*/
						// if(solver->value(tmp_l[0].var()) == l_Undef||solver->value(tmp_l[1].var())==l_Undef)
						//{ 
						solver->addXorClause(tmp_l, rhs_l );
						solver->additional_xor++;
						solver->findxor=true;
						//}
						 if  (!solver->ok)
						 { //printf("not-ok-739\n");
						  return solver->ok; }
					 }
				  else
				  {
					tmp_l.clear();
					/*printf("--------------------------------------------------------------------orig:");
				         for(uint32_t x=0;x<size;x++)
						{printf("%d%d ",origCl[x].var(),origCl[x].sign()); }
						printf("\n");*/
					if((bool)(now[0]&1)==(bool)(now[1]&1) )
					   {tmp_l.push(Lit(thetwo_var[0],(now[0]&1)));  
					    //printf("imply in two----------------: %d%d\n", tmp_l[0].var(),tmp_l[0].sign());
					   } 
					else if((bool)((now[0]>>1)&1)==(bool)((now[1]>>1)&1))
					  { 
					    tmp_l.push(Lit(thetwo_var[1],((now[1]>>1)&1)));
					    //printf("imply in two-----------: %d%d\n", tmp_l[0].var(),tmp_l[0].sign());
					  
					  }
					else
                      { // printf("must have at least one place be the same\n");
					  }	
					assert(tmp_l.size()==1);  
                    //if(solver->value(tmp_l[0].var()) == l_Undef||solver->value(tmp_l[1].var())==l_Undef)					  
					//{
					solver->addLearntClause(tmp_l);
					solver->additional_two++;
					solver->findxor=true;
					//}
						if  (!solver->ok)
					 { //printf("not-ok-752\n");
					  return solver->ok; } 
				  }
				}
				else if(now.size()==1)
				{
				  assert(now[0]<4);
				  tmp_l.clear();
				  tmp_l.push(Lit(thetwo_var[0],(now[0]&1)));
				  tmp_l.push(Lit(thetwo_var[1],((now[0]>>1)&1)));
				  bool al=false;
				  for(uint32_t u=0;u<alreadyfind.size();u++)
				  {
				    vector<Lit>& now_lit=alreadyfind[u];
					if(now_lit[0].toInt()==tmp_l[0].toInt())
					{
					   for(uint32_t k=1;k<now_lit.size();k++)
					     if(now_lit[k].toInt()==tmp_l[1].toInt())
                           {al=true;						 
					       break;}
					}
				     if(al) break;
				  }
				   if  (!solver->ok)
                 { //printf("not-ok-969\n");
				  return solver->ok; }
				  if(!al)
				  {
				  /* printf("--------------------------------------------------------------------orig:");
				  for(uint32_t x=0;x<size;x++)
				  {printf("%d%d ",origCl[x].var(),origCl[x].sign()); }
				  printf("\n");
				  printf("add one clause:%d%d %d%d\n", tmp_l[0].var(),tmp_l[0].sign(), tmp_l[1].var(), tmp_l[1].sign() );*/
				  //assert(al&&"----------\n");
				 
				  solver->addLearntClause(tmp_l);
				   if(solver->value(tmp_l[0].var()) == l_Undef||solver->value(tmp_l[1].var()) == l_Undef)
				  {
				  solver->additional_one++;
				  solver->findxor=true;
				  }
				 }
				  if  (!solver->ok)
                 { //printf("not-ok-763\n");
				  return solver->ok; }
				}
			 
	    }
		checklist_s.clear();
	}
	//printf("end of getmore\n");
	return true;
}

bool FoundXors::foundAll() 
{
    bool OK = true;
	odd_list.clear();
	even_list.clear();
	even_list_four.clear();
	odd_list_four.clear();
    for (uint32_t i = 0; i < foundComb.size(); i++) {
        //Only count combinations with the correct RHS
		//rhs=1 even number of true
		//odd=1 odd number of true
		bool odd=(NumberOfSetBits(i)%2);
		if(foundComb[i]){
		if(odd) {  odd_list.push_back(i); }
		else    {  even_list.push_back(i);}
		}
        if ((NumberOfSetBits(i)%2) == (uint32_t)(!rhs)) {
            continue;
        }

        //If this combination hasn't been found yet, then the XOR is not complete
        if (!foundComb[i]) {
            OK = false;
			if(size>4) break;
        }
    }

    #ifdef VERBOSE_DEBUG_XOR_FINDER
    if (OK) {
        cout << "Found all for this clause" << endl;
    }
    #endif
   
    return OK;
}

}


