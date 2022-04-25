#include "cmsat/EnhanceGaussian.h"

#include <set>
#include <iostream>
#include <iomanip>
#include "cmsat/Clause.h"
#include <algorithm>
#include "cmsat/ClauseCleaner.h"
#include "cmsat/DataSync.h"
#include "cmsat/VarReplacer.h"
#include "cmsat/time_mem.h"

using std::ostream;
using std::cout;
using std::endl; 
using std::set;

#ifdef VERBOSE_DEBUG
#include <iterator>
#endif

using namespace CMSat;



static const Var unassigned_col = std::numeric_limits<Var>::max();
//static const Var unassigned_var = std::numeric_limits<Var>::max();

EnhanceGaussian::EnhanceGaussian(Solver& _solver, const GaussConf& _config, const uint32_t _matrix_no, const vector<XorClause*>& _xorclauses) :
        solver(_solver)
        , config(_config)
        , matrix_no(_matrix_no)
		,disabled(false)
		, xorclauses(_xorclauses)
{
	clause_state_size =0;
	// some enhance gaussian information
	adjust_zero =0;
	adjust_one=0;
	adjust_two=0;
	conflict_two = 0;
	conflict_n = 0;
	propagate_two = 0;
	propagate = 0;
	already_true = 0;
	already_true_stop =0;
	el_conflict_two = 0;
	el_conflict =0;
	el_propagate_two= 0;
	el_propagate= 0;
	el_already_true =0;
	eliminate_num = 0;
	useful_conflict =0;
	delete_num_row = 0;
	find_truths_call = 0;
	called = 0;
}

EnhanceGaussian::~EnhanceGaussian()
{ 	
	for (uint32_t i = 0; i < clauses_toclear.size(); i++)
        solver.clauseAllocator.clauseFree(clauses_toclear[i].first);
 	if(clause_state_size > 0)		
		delete [] clause_state;
	
	//clause_map.clear();
}



void EnhanceGaussian::canceling(const uint32_t sublevel)
{	
	uint32_t a = 0;
    for (int i = clauses_toclear.size()-1; i >= 0 && clauses_toclear[i].second > sublevel; i--) {
		//printf("DD cancel %d %d\n", sublevel ,clauses_toclear[i].second )	;
		solver.clauseAllocator.clauseFree(clauses_toclear[i].first);
        a++;
    }
    clauses_toclear.resize(clauses_toclear.size()-a);
	memset(clause_state, 0, sizeof(uint64_t)*(clause_state_size) );
}

uint32_t EnhanceGaussian::select_columnorder(vector<Var>& var_to_col,matrixset& origMat) 
{
	// oringinal cryptominisat method
	var_to_col.resize(solver.nVars(), unassigned_col); 
    uint32_t num_xorclauses  = 0;
    for (uint32_t i = 0; i != xorclauses.size(); i++) {
        XorClause& c = *xorclauses[i];
        if (c.getRemoved()) continue;
        num_xorclauses++;
        for (uint32_t i2 = 0; i2 < c.size(); i2++) {
            assert(solver.assigns[c[i2].var()].isUndef());
            var_to_col[c[i2].var()] = unassigned_col - 1;
        }
    }
    uint32_t largest_used_var = 0;
    for (uint32_t i = 0; i < var_to_col.size(); i++)
        if (var_to_col[i] != unassigned_col)
            largest_used_var = i;
    var_to_col.resize(largest_used_var + 1);
	origMat.col_to_var.clear();
    vector<Var> vars(solver.nVars());
	if (!config.orderCols) {
		assert(false);  // I  think it would be there
        for (uint32_t i = 0; i < solver.nVars(); i++) {
            vars.push_back(i);
        }
        std::random_shuffle(vars.begin(), vars.end());
    }
	
    Heap<Solver::VarOrderLt> order_heap(solver.order_heap);
    uint32_t iterReduceIt = 0;
    while ((config.orderCols && !order_heap.empty()) || (!config.orderCols && iterReduceIt < vars.size()))
    {
        Var v;
        if (config.orderCols) v = order_heap.removeMin();
        else v = vars[iterReduceIt++];
        if (var_to_col[v] == 1) {
            origMat.col_to_var.push_back(v);
            var_to_col[v] = origMat.col_to_var.size()-1;
        }
    }

    //for the ones that were not in the order_heap, but are marked in var_to_col
    for (uint32_t v = 0; v != var_to_col.size(); v++) {
        if (var_to_col[v] == unassigned_col - 1) {
            origMat.col_to_var.push_back(v);
            var_to_col[v] = origMat.col_to_var.size() -1;
        }
    }	
	/*****************************************************************/
/*   	printf("Column variable index:\n");
	for(size_t i = 0 ; i< origMat.col_to_var.size() ; i++)
		printf("%d ",origMat.col_to_var[i]);
	printf("\n");
	
	printf("var_to_col index\n");
	for(size_t i = 0 ; i < var_to_col.size() ; i++)
		printf("%d ", var_to_col[i]);
	printf("\n");   */
	/*****************************************************************/
	
	
	return num_xorclauses;
}
void EnhanceGaussian::fill_matrix(matrixset& origMat)
{
	var_to_col.clear();
	
	// decide which variable in matrix column and the number of rows
	origMat.num_rows = select_columnorder(var_to_col,origMat);
	origMat.num_cols = origMat.col_to_var.size();
	
	origMat.matrix.resize(origMat.num_rows, origMat.num_cols);
	//only preprocess
	if(config.pre_two || config.pre_three) pre_matrix.resize(origMat.num_rows + 1, origMat.num_cols);
	
	
	uint32_t matrix_row = 0;
    for (uint32_t i = 0; i != xorclauses.size(); i++) {
        const XorClause& c = *xorclauses[i];
        if (c.getRemoved()) continue;
        origMat.matrix.getMatrixAt(matrix_row).set(c, var_to_col, origMat.num_cols);
       if(config.pre_two || config.pre_three)  pre_matrix.getMatrixAt(matrix_row).set(c, var_to_col, origMat.num_cols);
	   matrix_row++;
    }
	assert(origMat.num_rows == matrix_row);	
	
	// reset 
	GasVar_state.clear();
	GasVar_state.growTo(solver.nVars(), non_basic_var); // init varaible state 
	origMat.nb_rows.clear();
	origMat.nb2_rows.clear();
	for(size_t ii = 0 ; ii < solver.GausWatches.size() ; ii++){   //  delete gauss watch list
		solver.GausWatches[ii].clear();
	}
	clause_state_size = origMat.num_rows / 64 + (bool)( origMat.num_rows % 64);
	clause_state =  new uint64_t[clause_state_size];
	memset(clause_state, 0, sizeof(uint64_t)*(clause_state_size) );
	//printf("dd:Construct matrix by EnhanceGaussian::fill_matrix\n");
	//printf("DD %d:fill_matrix num_rows:%d  num_cols:%d\n",matrix_no,origMat.num_rows,origMat.num_cols);
	//print_matrix(origMat);
	

	
}


// return true is fine , return false means solver already false; 
const bool EnhanceGaussian::full_init(){
	//printf("DD:%d EnhanceGaussian::full_init start\n",matrix_no);
	assert(solver.ok);
    assert(solver.decisionLevel() == 0);
	gaussian_ret ret;
	
	solver.sum_Encalled++;
	//solver.gauss_called = true;
	
	
	
/* 	if(solver.gaussconfig.add_learn_two == 3){
		clause_map.clear();
		
		for(Var i = 0 ; i < solver.xorclauses.size() ; i++){			
			XorClause* ii = solver.xorclauses[i];
			if(ii->size() > 3)
				continue;
			assert(ii->size() == 3);
			
			string key;
			key += itos((*ii)[0].var());
			key += ",";	
			key += itos((*ii)[1].var());
			key += ",";	
			key += itos((*ii)[2].var());
			
			clause_map.insert( pair<string,bool>(key,true) );
			//cout << "key:"<<key << endl;
		}
		
		
	} */	
	
	
	//bool do_again_gauss = true;
	 
	//while (do_again_gauss) {
		//do_again_gauss = false;
		solver.clauseCleaner->cleanClauses(solver.xorclauses, ClauseCleaner::xorclauses);
		if (!solver.ok) return false;
		
		fill_matrix(cur_matrixset);  // construct matrix
		if (!cur_matrixset.num_rows || !cur_matrixset.num_cols) {
			assert(false);   // I am not sure this condition can appear ???? , so test
		}
		
		if(solver.gauss_called ==false && config.pre_two){
			double  pretime = cpuTime();
			preprecessing();
			printf("preptime2: %f\t", cpuTime() - pretime);
			
			
			solver.clauseCleaner->cleanClauses(solver.xorclauses, ClauseCleaner::xorclauses);
			if (!solver.ok) return false;
		
			fill_matrix(cur_matrixset);  // construct matrix
			if (!cur_matrixset.num_rows || !cur_matrixset.num_cols) {
				assert(false);   // I am not sure this condition can appear ???? , so test
			}
			
		}
		if(solver.gauss_called ==false && config.pre_three){
			double  pretime = cpuTime();
			preprecessing_3();
			printf("preptime3: %f\t", cpuTime() - pretime);
			
			
			solver.clauseCleaner->cleanClauses(solver.xorclauses, ClauseCleaner::xorclauses);
			if (!solver.ok) return false;
		
			fill_matrix(cur_matrixset);  // construct matrix
			if (!cur_matrixset.num_rows || !cur_matrixset.num_cols) {
				assert(false);   // I am not sure this condition can appear ???? , so test
			}
			
		}
		
		solver.gauss_called = true;
		
		eliminate(cur_matrixset);  // gauss eliminate algorithm
		ret = adjust_matrix(cur_matrixset);  // find some row already true false, and insert watch list
		switch (ret){
			case conflict:
				solver.ok = false; 
				//solver.sum_unit++; 
				solver.sum_Enconflict++;
				return false;
				break;
			case unit_propagation:
				//do_again_gauss = true;
				//solver.ok = (solver.propagate<true>().isNULL());
				solver.sum_Enpropagate++;
				for(uint32_t i = 0 ; i < prpagation_lit.size() ; i++){
					solver.uncheckedEnqueue(prpagation_lit[i]);  // propagation
				}
				solver.ok = (solver.propagate<true>().isNULL());
				if (!solver.ok) return false;
				break;
			default:
				break;
		}
	//}	
	//clause_state_size = cur_matrixset.num_rows / 64 + (bool)( cur_matrixset.num_rows % 64);
	//clause_state =  new uint64_t[clause_state_size];
	//memset(clause_state, 0, sizeof(uint64_t)*(clause_state_size) );

	//printf("dd %d:final num_rows:%d  num_cols:%d\n",matrix_no,cur_matrixset.num_rows,cur_matrixset.num_cols);
	//exit(1);
	//printf("DD:%d EnhanceGaussian::full_init end\n",matrix_no);
	//printf_state();
	//print_matrix(cur_matrixset);
	//Debug_funtion();
	//exit(1);
	
	return true;
}


void EnhanceGaussian::eliminate(matrixset& m){
	//printf("dd:gaussian eliminate algorithm start\n");
	uint32_t i = 0;
    uint32_t j = 0;
	//uint32_t k = 0;
    PackedMatrix::iterator end = m.matrix.beginMatrix() + m.num_rows;
	PackedMatrix::iterator rowIt = m.matrix.beginMatrix();
	
	while (i != m.num_rows && j != m.num_cols) {
		PackedMatrix::iterator this_matrix_row = rowIt;
        for (; this_matrix_row != end; ++this_matrix_row) {
            if ((*this_matrix_row)[j])
                break;
        }	
		if (this_matrix_row != end) {
			//swap rows 
            if (this_matrix_row != rowIt) {
                (*rowIt).swapBoth(*this_matrix_row);
            }
			// diagnose row
			for (PackedMatrix::iterator k_row = m.matrix.beginMatrix(); k_row != end; ++k_row)  {
                //subtract row i from row u;
                //Now A[u,j] will be 0, since A[u,j] - A[i,j] = A[u,j] -1 = 0.
				if(k_row != rowIt){
					if ((*k_row)[j]){
						(*k_row).xorBoth(*rowIt);
					}
				}
            }
			i++;
            ++rowIt;
			GasVar_state[m.col_to_var[j]] = basic_var;   // this column is basic variable
			//printf("basic var:%d\n",m.col_to_var[j] + 1);	
		}
		j++;
	}
	//printf("dd:matrix by EnhanceGaussian::eliminate\n");
	//print_matrix(m);
	//printf("dd:gaussian eliminate algorithm end\n");
}


EnhanceGaussian::gaussian_ret EnhanceGaussian::adjust_matrix(matrixset& m){
	//printf("\n dd:adjust_matrix start\n");
	
	PackedMatrix::iterator end = m.matrix.beginMatrix() + m.num_rows;
	PackedMatrix::iterator rowIt = m.matrix.beginMatrix();
	uint32_t row_id = 0;
	uint32_t nb_var = 0;
	uint32_t nb_var2 = 0;  // non-basic 2 variable
	bool  xorEqualFalse;
	gaussian_ret adjust_ret = nothing;
	adjust_zero = 0;
	prpagation_lit.clear();
	//printf("DD:%d %d\n", solver.qhead  ,solver.trail.size());
	uint32_t switch_condition = 0;  // switch condition 
	//row_three.clear();
	
	while( rowIt != end ){
						//(vec<Lit>& tmp_clause, const vector<Var>& col_to_var,vec<bool> &GasVar_state , uint32_t& nb_var )
		//switch((*rowIt).find_watchVar(tmp_clause,cur_matrixset.col_to_var,GasVar_state,nb_var)){
		if(config.add_learn_three == 3){
		//find_watchVar_2(vec<Lit>& tmp_clause, const vector<Var>& col_to_var,vec<bool> &GasVar_state , uint32_t& nb_var, uint32_t& nb_var2 )
			switch_condition = (*rowIt).find_watchVar_2(tmp_clause,cur_matrixset.col_to_var,GasVar_state,nb_var,nb_var2);
		}else{
			switch_condition = (*rowIt).find_watchVar(tmp_clause,cur_matrixset.col_to_var,GasVar_state,nb_var);
		}	
		//row_three.push(false);
		switch(switch_condition){	
			case 0: // this row is all zero
				//printf("%d:Warring: this row is all zero in adjust matrix\n",row_id);
				adjust_zero++; // information
				//row_size.push(0);
				if( (*rowIt).is_true() ){	  // conflic
					//printf("%d:Warring: this row is conflic in adjust matrix!!!",row_id);
					return conflict;
				}
				break;
			case 1:{	// this row neeed to propogation
				//printf("%d:This row only one variable, need to propogation!!!! in adjust matrix\n",row_id);	
				
				solver.cancelUntil(0);
				xorEqualFalse = !m.matrix.getMatrixAt(row_id).is_true();
				tmp_clause[0] = Lit( tmp_clause[0].var() , xorEqualFalse) ;
				//solver.uncheckedEnqueue(tmp_clause[0]);  // propagation
				prpagation_lit.push(tmp_clause[0]); 
				//std::cout << "dd:" <<tmp_clause[0]  << std::endl ;
				assert(solver.value( tmp_clause[0] .var()).isUndef());
				(*rowIt).setZero();// reset this row all zero
				m.nb_rows.push(std::numeric_limits<uint32_t>::max()); // delete non basic value in this row
				if(config.add_learn_three == 3 ) m.nb2_rows.push(std::numeric_limits<uint32_t>::max()); // delete non basic value in this row
				GasVar_state[tmp_clause[0].var()] = non_basic_var;   // delete basic value in this row
				adjust_ret = unit_propagation;
				solver.init_sum_unit++;  // information
				//row_size.push(1);
				//return unit_propagation;
				break;
			}
			case 2:{	// this row have to variable
				//printf("%d:This row have two variable!!!! in adjust matrix\n",row_id);
				//std::cout << "dd:" <<tmp_clause[0].var() << " " << tmp_clause[1].var() << std::endl ;
				xorEqualFalse = !m.matrix.getMatrixAt(row_id).is_true();
				propagation_twoclause(xorEqualFalse);
				(*rowIt).setZero();// reset this row all zero
				m.nb_rows.push(std::numeric_limits<uint32_t>::max());	// delete non basic value in this row
				if(config.add_learn_three == 3) m.nb2_rows.push(std::numeric_limits<uint32_t>::max()); // delete non basic value in this row
				GasVar_state[tmp_clause[0].var()] = non_basic_var;   // delete basic value in this row
				adjust_ret = unit_propagation;
				solver.init_sum_unit++;  // information 
				//row_size.push(2);
				//return unit_propagation;
				break;
			}
			default: // need to update watch list
				//printf("%d:need to update watch list\n",row_id);			
				assert(nb_var != std::numeric_limits<uint32_t>::max());
				assert(nb_var != tmp_clause[0].var());
				
				// insert watch list
				solver.GausWatches[tmp_clause[0].var() ].push(Solver::GausWatched(row_id,matrix_no));
				solver.GausWatches[nb_var].push(Solver::GausWatched(row_id,matrix_no));
				m.nb_rows.push(nb_var);	// record in this row non_basic variable
				
				if(config.add_learn_three == 3 ){
					assert(nb_var2 != std::numeric_limits<uint32_t>::max());
					assert(nb_var != nb_var2);
					assert( tmp_clause[0].var() != nb_var2);
					
					solver.GausWatches[nb_var2].push(Solver::GausWatched(row_id,matrix_no));				 // insert non-basic 2 variable
					m.nb2_rows.push(nb_var2); // record in this row non_basic 2 variable
				}
				//row_size.push(tmp_clause.size());
				
				// add for learn clause
				
				if(tmp_clause.size() == solver.gaussconfig.add_learn_two){
					add_learn_two(!m.matrix.getMatrixAt(row_id).is_true() , row_id );	
				}	
				
				
				break;
		}
		++rowIt;
		row_id++;
		
		
	}
	//printf("DD:nb_rows:%d %d %d\n",m.nb_rows.size() ,   row_id - adjust_zero  ,  adjust_zero);
	assert(m.nb_rows.size() == row_id - adjust_zero);
	
	
	m.matrix.resizeNumRows(row_id - adjust_zero);
	m.num_rows = row_id - adjust_zero;
	if(!solver.Is_Gauss_first) { solver.sum_Encalled_eliminate = adjust_zero ;  solver.Is_Gauss_first = true ;}
	//m.abort_rows.resize(num_row);
	//delete_num_row = m.num_rows - num_row; // information
	//printf("DD: adjust number of Row:%d  %d\n",m.num_rows, m.num_cols);
	//printf("dd:matrix by EnhanceGaussian::adjust_matrix\n");
	//print_matrix(m);
	//printf("dd:adjust_matrix end\n");
	//Debug_funtion();
	return adjust_ret;
}

inline void EnhanceGaussian::delete_gausswatch(const bool orig_basic , const uint16_t  row_n)
{
	// Delete this row because we have already add to xor clause, nothing to do anymore	
	if(orig_basic){  // clear nonbasic value watch list
		bool debug_find = false;
		vec<Solver::GausWatched>&  ws_t  =  solver.GausWatches[ cur_matrixset.nb_rows[row_n] ];
		for(int tmpi = ws_t.size() - 1 ; tmpi >= 0 ; tmpi--){
			if(ws_t[tmpi].row_id == row_n){
				ws_t[tmpi] = ws_t.last();
				 ws_t.shrink(1);
				 debug_find = true;
				 break;
			}
		}
		assert(debug_find);
	}else{
		assert( solver.GausWatches[  tmp_clause[0].var() ].size()== 1 );
		solver.GausWatches[  tmp_clause[0].var() ].clear();
	}	
	
}



inline void EnhanceGaussian::conflict_twoclause(PropBy& confl)
{
	//assert(tmp_clause.size() == 2);
	//printf("dd %d:This row is conflict two\n",row_n);
	//std::cout << "dd:" <<tmp_clause[0].var()  << " " << tmp_clause[1].var()  << std::endl ;
	
	Lit lit1 = tmp_clause[0];
	Lit lit2 = tmp_clause[1];

	solver.watches[(~lit1).toInt()].push(Watched(lit2, true));
	solver.watches[(~lit2).toInt()].push(Watched(lit1, true));
	solver.numBins++;
	solver.learnts_literals += 2;
	solver.dataSync->signalNewBinClause(lit1, lit2);

	lit1 = ~lit1;
	lit2 = ~lit2;
	solver.watches[(~lit2).toInt()].push(Watched(lit1, true));
	solver.watches[(~lit1).toInt()].push(Watched(lit2, true));
	solver.numBins++;
	solver.learnts_literals += 2;
	solver.dataSync->signalNewBinClause(lit1, lit2);

	lit1 = ~lit1;
	lit2 = ~lit2;

	confl = PropBy(lit1);
	solver.failBinLit = lit2;
}

inline void EnhanceGaussian::propagation_twoclause(const bool xorEqualFalse)
{
	//printf("DD:%d %d\n", solver.qhead  ,solver.trail.size());
	//std::cout << "dd:" <<tmp_clause[0].var()  << " " << tmp_clause[1].var()  << std::endl ;
	
	tmp_clause[0] = tmp_clause[0].unsign();
	tmp_clause[1] = tmp_clause[1].unsign();
	XorClause* cl = solver.addXorClauseInt(tmp_clause, xorEqualFalse, 0);
	release_assert(cl == NULL);
	release_assert(solver.ok);
	//printf("DD:x%d %d\n",tmp_clause[0].var() , tmp_clause[1].var());
}




bool  EnhanceGaussian::find_truths(const vec<Solver::GausWatched>::iterator &i, vec<Solver::GausWatched>::iterator &j,Var p ,PropBy& confl, const uint16_t row_n 
								   ,bool &do_eliminate , Var &e_var , uint16_t &e_row_n )
{
	//printf("dd ~~~~~~~~EnhanceGaussian:: find_truths start ~~~~~~~~~~~~\n");
	//printf("dd Watch variable : %d  ,  Wathch row num %d\n", p , row_n);
	release_assert(solver.ok);
	
	
	uint32_t nb_var = 0; // nobasic variable colunt
	int  ret;
	
	e_var = std::numeric_limits<uint32_t>::max();
	e_row_n = std::numeric_limits<uint16_t>::max();
	do_eliminate = false;
	bool xorEqualFalse ;
	PackedMatrix::iterator rowIt = cur_matrixset.matrix.beginMatrix() + row_n;
	
 	// if this clause is alreadt true
 	if((clause_state[row_n/64] >> (row_n%64)) & 1){
		*j++ = *i;  // store watch list
		return true;
	}  	
	
	bool orig_basic = false;
	if( GasVar_state[p]){  // swap basic and non_basic variable 
		orig_basic = true;
		GasVar_state[ cur_matrixset.nb_rows[row_n] ]  = basic_var;
		GasVar_state[ p ]  = non_basic_var;
	}

	//propGause(vec<Lit>& tmp_clause,const vec<lbool>& assigns, const vector<Var>& col_to_var, vec<bool> &GasVar_state ,uint32_t& nb_var , uint32_t start)
	ret = (*rowIt).propGause(tmp_clause,solver.assigns,cur_matrixset.col_to_var, GasVar_state ,nb_var ,  var_to_col[p]);
	
	
	switch(ret){
	// gaussian state     0         1              2            3                4
	//enum gaussian_ret {conflict, unit_conflict, propagation, unit_propagation, nothing};
	case 0:{
		//assert((*rowIt).popcnt() == tmp_clause.size());
		//printf("dd %d:This row is conflict %d\n",row_n , solver.level[p] );	
		if (tmp_clause.size() == 2) {
			//printf("%d:This row is conflict two\n",row_n);
			solver.sum_unit++;
			
			delete_gausswatch(orig_basic , row_n);  // delete watch list
			GasVar_state[tmp_clause[0].var()] = non_basic_var; // delete value state;               
			GasVar_state[ tmp_clause[1].var() ] = non_basic_var;		
			cur_matrixset.nb_rows[row_n] = std::numeric_limits<uint32_t>::max(); // delete non basic value in this row	
			(*rowIt).setZero();// reset this row all zero
			
			conflict_twoclause(confl);  // get two conflict  clause
			
		}else{
			*j++ = *i;
			xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(row_n).is_true();
			Clause* conflPtr = (Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, xorEqualFalse);
			confl = solver.clauseAllocator.getOffset(conflPtr);						
			
/* 			Clause& cla = *conflPtr; // Debug conflict clause		
  			for (uint32_t ii = 0, size = cla.size(); ii != size; ii++){
				assert(solver.level[cla[ii].var()] <= solver.level[cla[0].var()]);
			}  */
			
			if( orig_basic){   // recover
				GasVar_state[ cur_matrixset.nb_rows[row_n] ]  = non_basic_var;
				GasVar_state[ p ]  = basic_var;
			}
		}
		solver.qhead = solver.trail.size();
		solver.Gauseqhead = solver.trail.size();
		return false;
	}
	case 2:{
		//assert((*rowIt).popcnt() == tmp_clause.size());
		//printf("%d:This row is propagation : level: %d\n",row_n, solver.level[p]);
		xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(row_n).is_true();
		if(tmp_clause.size() == 2){
			//printf("%d:This row is propagation two\n",row_n);
			//assert((*rowIt).popcnt() == 2);
			solver.sum_unit++;
			
			delete_gausswatch(orig_basic , row_n);  // delete watch list		
			GasVar_state[tmp_clause[0].var()] = non_basic_var; // delete value state;               
			GasVar_state[ tmp_clause[1].var() ] = non_basic_var;		
			cur_matrixset.nb_rows[row_n] = std::numeric_limits<uint32_t>::max(); // delete non basic value in this row	
			(*rowIt).setZero();// reset this row all zero
			solver.cancelUntil(0);
			propagation_twoclause(xorEqualFalse); // propagation two clause
			return false;
		}
		*j++ = *i;  // store watch list
		
		if (solver.decisionLevel() == 0) {
			solver.uncheckedEnqueue(tmp_clause[0]);
		}else{	
			
		     // delete by hankf4 for add learnt clause
			 Clause& cla = *(Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, xorEqualFalse);
			//cla.print();	
			//Clause& cla =*(Clause*)solver.clauseAllocator.Clause_new(tmp_clause, solver.learnt_clause_group++);
			clauses_toclear.push_back(std::make_pair(&cla, solver.trail.size()-1));		
			assert(!(cla.getFreed()));
			assert(solver.assigns[cla[0].var()].isUndef());
			solver.uncheckedEnqueue(cla[0], solver.clauseAllocator.getOffset(&cla)); 
			
			
			/********************************  for add learnt clause *******************************************/ 
 		/* 	Clause& cla = *(Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, xorEqualFalse, solver.learnt_clause_group++);
			if( cla.size() <= solver.gaussconfig.add_learn_two  && solver.Gauss_learnts.size() <=  solver.gaussconfig.gauss_learn_threshold){
				//Clause* cla = solver.clauseAllocator.Clause_new(tmp_clause, true);
				solver.Gauss_learnts.push(&cla); // add for learn clause  			
				//solver.learnts.push(&cla);
				cla.setGlue(MAX_THEORETICAL_GLUE);
				solver.attachClause(cla);
			}else{ 
				//cla.print();	 // for debug
				clauses_toclear.push_back(std::make_pair(&cla, solver.trail.size()-1)); // delete for test add learn clause in 4/25
			}
			assert(!(cla.getFreed()));
			assert(solver.assigns[cla[0].var()].isUndef());
			solver.uncheckedEnqueue(cla[0], solver.clauseAllocator.getOffset(&cla));  */
			
			
			/*****************************************************************************************************/ 
			
			
			
		}
		if(orig_basic){   // recover
			GasVar_state[ cur_matrixset.nb_rows[row_n] ]  = non_basic_var;
			GasVar_state[ p ]  = basic_var;
		}
 		// record this clause is already true
		clause_state[row_n/64] |= ((uint64_t)1 << (row_n%64));
		return true;
	}
	case 5:   // find new watch list
		//printf("%d:This row is find new watch:%d => orig %d p:%d\n",row_n , nb_var,orig_basic , p); 
		assert(nb_var != std::numeric_limits<uint32_t>::max()); 
		if(orig_basic)
			solver.GausWatches[nb_var].clear(); ///clear orignal gausWatch list , because only one basic value in gausWatch list
		solver.GausWatches[nb_var].push(Solver::GausWatched( row_n ,matrix_no)); // update gausWatch list
		if(!orig_basic){
			cur_matrixset.nb_rows[row_n] = nb_var; // update in this row non_basic variable 
			return true;
		}
		GasVar_state[ cur_matrixset.nb_rows[row_n] ] = non_basic_var;// recover non_basic variable 
		GasVar_state[nb_var] = basic_var; // set basic variable	
		e_var = nb_var; // store the eliminate valuable    
		e_row_n = row_n;
		break;
	case 4: // this row already treu
		//printf("%d:This row is nothing( maybe already true) \n",row_n);
		*j++ = *i;  // store watch list
		if(orig_basic){   // recover
			GasVar_state[ cur_matrixset.nb_rows[row_n] ]  = non_basic_var;
			GasVar_state[ p ]  = basic_var;
		}
		clause_state[row_n/64] |= ((uint64_t)1 << (row_n%64)); // record this clause is already true
		return true;
	default:
		assert(false);  // can not here 
		break;
	}
	
/* 	assert(e_var != std::numeric_limits<uint32_t>::max());
	assert(e_row_n != std::numeric_limits<uint16_t>::max());
	assert(orig_basic);
	assert(ret == 5 );
	assert(solver.GausWatches[e_var].size() == 1);
	 */
	do_eliminate = true;
	return true;
}



void EnhanceGaussian::eliminate_col(Var e_var  ,uint16_t e_row_n ,Var p,PropBy& confl){

	//cout << "eliminate this column :" << e_var  << " " << p << " " << e_row_n <<  endl;
	//eliminate_num++ ; // undate information
	PackedMatrix::iterator this_row = cur_matrixset.matrix.beginMatrix() + e_row_n;
	PackedMatrix::iterator rowI = cur_matrixset.matrix.beginMatrix();
	PackedMatrix::iterator end = cur_matrixset.matrix.endMatrix(); 
	int ret;
	uint32_t e_col = var_to_col[e_var];
	uint32_t ori_nb = 0 , ori_nb_col = 0;
	uint32_t nb_var = 0;
	uint32_t num_row = 0;   // row inde
	bool xorEqualFalse = false ;
	bool conflict_bol = false;
	bool conflict_two = false;
	uint32_t conflict_size = UINT_MAX;
	
	uint32_t row_size = 0 ;
	
	while( rowI != end ){
		if((*rowI)[e_col] &&  this_row !=  rowI ){
			// detect orignal non basic watch list change or not
			ori_nb = cur_matrixset.nb_rows[num_row];
			ori_nb_col = var_to_col[ ori_nb ] ;	
			assert((*rowI)[ori_nb_col]);
			
			(*rowI).xorBoth(*this_row);  // xor eliminate		
			
			if(!(*rowI)[ori_nb_col]){  // orignal non basic value is eliminate
				if( ori_nb != e_var)   // delelte orignal non basic value in wathc list
					delete_gausswatch(true , num_row);
				
				if(solver.gaussconfig.add_pre == true)				
					ret = (*rowI).propGause(tmp_clause,solver.assigns,cur_matrixset.col_to_var, GasVar_state ,nb_var , ori_nb_col);
				 else{
					ret = (*rowI).propGause_add_learnt_two(tmp_clause,solver.assigns,cur_matrixset.col_to_var, GasVar_state ,nb_var , ori_nb_col,row_size);
					if(row_size == solver.gaussconfig.add_learn_two ){
						add_learn_two(!cur_matrixset.matrix.getMatrixAt(num_row).is_true(), num_row);
						//row_three[num_row] = true;						
					}	
				} 
				switch(ret){
				case 0:{ // conflict
					//printf("%d:This row is conflict in eliminate col\n",num_row);
					if(tmp_clause.size() >= conflict_size) {
						solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
						cur_matrixset.nb_rows[num_row] = p; // // update in this row non_basic variable
						break;
				    }
					conflict_size = tmp_clause.size()  ;
					if ( conflict_size == 2) {
						//printf("%d:This row is conflict two in eliminate col\n",num_row);
						solver.sum_unit++;
						
						delete_gausswatch(false ,num_row );  
						assert(GasVar_state[tmp_clause[0].var()] ==  basic_var); assert(GasVar_state[tmp_clause[1].var()] ==  non_basic_var); 
						GasVar_state[tmp_clause[0].var()] = non_basic_var; // delete value state;               
						cur_matrixset.nb_rows[num_row] = std::numeric_limits<uint32_t>::max(); // delete non basic value in this row	
						(*rowI).setZero();// reset this row all zero
						
						conflict_twoclause(confl);  // get two conflict  clause						
					
						conflict_two = true;	
					}else{
						solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
						cur_matrixset.nb_rows[num_row] = p; // // update in this row non_basic variable
						
						xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(num_row).is_true();
						tmp_clause.copyTo(conflict_clause);
					}
					conflict_bol = true;
					break;
				}
				case 2:{
					//printf("%d:This row is propagation in eliminate col\n",num_row);
					if(conflict_bol){  // update no_basic_value
						solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no));
						cur_matrixset.nb_rows[num_row] = p;
						break;
					}
					xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(num_row).is_true();
 					if(tmp_clause.size() == 2){
						//printf("%d:This row is propagation two in eliminate col\n",num_row);
						solver.sum_unit++;
						
						delete_gausswatch(false , num_row);  // delete watch list		
						assert(GasVar_state[tmp_clause[0].var()] ==  basic_var); assert(GasVar_state[tmp_clause[1].var()] ==  non_basic_var); 
						GasVar_state[tmp_clause[0].var()] = non_basic_var; // delete value state;               	
						cur_matrixset.nb_rows[num_row] = std::numeric_limits<uint32_t>::max(); // delete non basic value in this row	
						(*rowI).setZero();// reset this row all zero
						solver.cancelUntil(0);
						propagation_twoclause(xorEqualFalse); // propagation two clause
					}else{ 
						solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no));// update no_basic information
						cur_matrixset.nb_rows[num_row] = p;
						
						if (solver.decisionLevel() == 0) {
							solver.uncheckedEnqueue(tmp_clause[0]);
						}else{	
							// delete for adding learn clause
							 Clause& cla = *(Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, xorEqualFalse);
							clauses_toclear.push_back(std::make_pair(&cla, solver.trail.size()-1));		
							assert(!(cla.getFreed()));
							assert(solver.assigns[cla[0].var()].isUndef());
							solver.uncheckedEnqueue(cla[0], solver.clauseAllocator.getOffset(&cla)); 
							
						/* 	Clause& cla = *(Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, xorEqualFalse, solver.learnt_clause_group++);
							
							 if( cla.size() <= solver.gaussconfig.add_learn_two  && solver.Gauss_learnts.size() <=  solver.gaussconfig.gauss_learn_threshold){
								//Clause* cla = solver.clauseAllocator.Clause_new(tmp_clause, true);
								solver.Gauss_learnts.push(&cla); // add for learn clause  			
								//solver.learnts.push(&cla);
								cla.setGlue(MAX_THEORETICAL_GLUE);
								solver.attachClause(cla);								
							}else{ 
								//Clause& cla = *(Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, xorEqualFalse);  // delete for test add learn clause in 4/25
								//cla.print();	 // for debug
								clauses_toclear.push_back(std::make_pair(&cla, solver.trail.size()-1)); // delete for test add learn clause in 4/25
							}
							assert(!(cla.getFreed()));
							assert(solver.assigns[cla[0].var()].isUndef());
							solver.uncheckedEnqueue(cla[0], solver.clauseAllocator.getOffset(&cla)); */
						}
						// record this clause is already true
						clause_state[num_row/64] |= ((uint64_t)1 << (num_row%64));
					}
				
					break;
				}
				case 5:   // find new watch list
					//printf("%d::This row find new watch list :%d in eliminate col\n",num_row,nb_var);
					solver.GausWatches[nb_var].push(Solver::GausWatched(num_row,matrix_no));// update gausWatch list
					cur_matrixset.nb_rows[num_row] = nb_var;			
					break;
				case 4: // this row already tre
					//printf("%d:This row is nothing( maybe already true) in eliminate col\n",num_row);	
					solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list
					cur_matrixset.nb_rows[num_row] = p;// update in this row non_basic variable
					clause_state[num_row/64] |= ((uint64_t)1 << (num_row%64));// record this clause is already true
					break;
				default:
					// can not here 
					assert(false);										
						break;
				}
			}
			
		}			
		++rowI;
		num_row++;
	}
	
	if(conflict_bol && !conflict_two ){
		//xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(num_row).is_true();
		Clause* conflPtr = (Clause*)solver.clauseAllocator.XorClause_new(conflict_clause, xorEqualFalse);
		confl = solver.clauseAllocator.getOffset(conflPtr);
		solver.qhead = solver.trail.size();
		solver.Gauseqhead = solver.trail.size();
		
/* 		// Debug conflict clause
		Clause& cla = *conflPtr;
		for (uint32_t ii = 0, size = cla.size(); ii != size; ii++){
			assert(solver.level[cla[ii].var()] <= solver.level[cla[0].var()]);
		}   */ 
	}
	//Debug_funtion();
}



bool  EnhanceGaussian::find_truths3(const vec<Solver::GausWatched>::iterator &i, vec<Solver::GausWatched>::iterator &j,Var p ,PropBy& confl, const uint16_t row_n 
								   ,bool &do_eliminate , Var &e_var , uint16_t &e_row_n )
{
	//printf("dd ~~~~~~~~EnhanceGaussian:: find_truths start ~~~~~~~~~~~~\n");
	//printf("dd Watch variable : %d  ,  Wathch row num %d\n", p , row_n);
	
	uint32_t nb_var = 0; // nobasic variable colunt
	uint32_t nb2_var =  cur_matrixset.nb2_rows[row_n]; // this row's non-basic var 2 
	int  ret;
	bool  nb2_condition= false;  // for check three watch condition
	e_var = std::numeric_limits<uint32_t>::max();
	e_row_n = std::numeric_limits<uint16_t>::max();
	do_eliminate = false;
	bool xorEqualFalse ;
	PackedMatrix::iterator rowIt = cur_matrixset.matrix.beginMatrix() + row_n;
	
 	// if this clause is alreadt true
 	if((clause_state[row_n/64] >> (row_n%64)) & 1){
		*j++ = *i;  // store watch list
		return true;
	}  	
	
	bool orig_basic = false;
	if( GasVar_state[p]){  // swap basic and non_basic variable 
		orig_basic = true;
		GasVar_state[ cur_matrixset.nb_rows[row_n] ]  = basic_var;
		GasVar_state[ p ]  = non_basic_var;
	}else if(p == nb2_var)
		nb2_condition = true;
	

	//propGause(vec<Lit>& tmp_clause,const vec<lbool>& assigns, const vector<Var>& col_to_var, vec<bool> &GasVar_state ,uint32_t& nb_var , uint32_t start)
	//ret = (*rowIt).propGause(tmp_clause,solver.assigns,cur_matrixset.col_to_var, GasVar_state ,nb_var ,  var_to_col[p]);
    if( !nb2_condition ){ 
		ret = (*rowIt).propGause2(tmp_clause,solver.assigns, cur_matrixset.col_to_var, GasVar_state ,nb_var , var_to_col[p] , nb2_var );
	}else { // nb 2 
		ret = (*rowIt).propGause2(tmp_clause,solver.assigns, cur_matrixset.col_to_var, GasVar_state ,nb_var , var_to_col[p] , cur_matrixset.nb_rows[row_n]  );
	}
	
	switch(ret){
	// gaussian state     0         1              2            3                4
	//enum gaussian_ret {conflict, unit_conflict, propagation, unit_propagation, nothing};
	case 0:{
		//assert((*rowIt).popcnt() == tmp_clause.size());
	//	printf("dd %d:This row is conflict %d\n",row_n , solver.level[p] );	
		if (tmp_clause.size() == 2) {
		//	printf("%d:This row is conflict two\n",row_n);
			solver.sum_unit++;
			
			delete_gausswatch(orig_basic , row_n);  // delete watch list
			GasVar_state[tmp_clause[0].var()] = non_basic_var; // delete value state;               
			GasVar_state[ tmp_clause[1].var() ] = non_basic_var;		
			cur_matrixset.nb_rows[row_n] = std::numeric_limits<uint32_t>::max(); // delete non basic value in this row	
			cur_matrixset.nb2_rows[row_n] = std::numeric_limits<uint32_t>::max(); // delete non basic 2 value in this row	
			(*rowIt).setZero();// reset this row all zero
			
			conflict_twoclause(confl);  // get two conflict  clause
			
		}else{
			*j++ = *i;
			xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(row_n).is_true();
			Clause* conflPtr = (Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, xorEqualFalse);
			confl = solver.clauseAllocator.getOffset(conflPtr);						
			
/* 			Clause& cla = *conflPtr; // Debug conflict clause		
  			for (uint32_t ii = 0, size = cla.size(); ii != size; ii++){
				assert(solver.level[cla[ii].var()] <= solver.level[cla[0].var()]);
			}  */
			
			if( orig_basic){   // recover
				GasVar_state[ cur_matrixset.nb_rows[row_n] ]  = non_basic_var;
				GasVar_state[ p ]  = basic_var;
			}
		}
		solver.qhead = solver.trail.size();
		solver.Gauseqhead = solver.trail.size();
		return false;
	}
	case 2:{
		//assert((*rowIt).popcnt() == tmp_clause.size());
	//	printf("%d:This row is propagation : level: %d\n",row_n, solver.level[p]);
		xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(row_n).is_true();
		if(tmp_clause.size() == 2){
		//	printf("%d:This row is propagation two\n",row_n);
			//assert((*rowIt).popcnt() == 2);
			solver.sum_unit++;
			
			delete_gausswatch(orig_basic , row_n);  // delete watch list		
			GasVar_state[tmp_clause[0].var()] = non_basic_var; // delete value state;               
			GasVar_state[ tmp_clause[1].var() ] = non_basic_var;		
			cur_matrixset.nb_rows[row_n] = std::numeric_limits<uint32_t>::max(); // delete non basic value in this row	
			cur_matrixset.nb2_rows[row_n] = std::numeric_limits<uint32_t>::max(); // delete non basic 2 value in this row				
			(*rowIt).setZero();// reset this row all zero
			solver.cancelUntil(0);
			propagation_twoclause(xorEqualFalse); // propagation two clause
			return false;
		}
		*j++ = *i;  // store watch list
		
		if (solver.decisionLevel() == 0) {
			solver.uncheckedEnqueue(tmp_clause[0]);
		}else{	
			Clause& cla = *(Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, xorEqualFalse);
			//cla.print();	
			//Clause& cla =*(Clause*)solver.clauseAllocator.Clause_new(tmp_clause, solver.learnt_clause_group++);
			clauses_toclear.push_back(std::make_pair(&cla, solver.trail.size()-1));		
			assert(!(cla.getFreed()));
			assert(solver.assigns[cla[0].var()].isUndef());
			solver.uncheckedEnqueue(cla[0], solver.clauseAllocator.getOffset(&cla));
		}
		if(orig_basic){   // recover
			GasVar_state[ cur_matrixset.nb_rows[row_n] ]  = non_basic_var;
			GasVar_state[ p ]  = basic_var;
		}
 		// record this clause is already true
		clause_state[row_n/64] |= ((uint64_t)1 << (row_n%64));
		return true;
	}
	case 5:   // find new watch list
	//	printf("%d:This row is find new watch:%d => orig %d p:%d\n",row_n , nb_var,orig_basic , p); 
		assert(nb_var != std::numeric_limits<uint32_t>::max()); 
		
		
		if(orig_basic)
			solver.GausWatches[nb_var].clear(); ///clear orignal gausWatch list , because only one basic value in gausWatch list
		solver.GausWatches[nb_var].push(Solver::GausWatched( row_n ,matrix_no)); // update gausWatch list
		
/* 		if(!orig_basic){
			cur_matrixset.nb_rows[row_n] = nb_var; // update in this row non_basic variable 
			return true;
		} */
		if(!orig_basic){
			if(!nb2_condition)
				cur_matrixset.nb_rows[row_n] = nb_var; // update in this row non_basic variable 
			else {
				cur_matrixset.nb2_rows[row_n] = nb_var; // update in this row non_basic variable 
			}
			return true;
		}
		
		GasVar_state[ cur_matrixset.nb_rows[row_n] ] = non_basic_var;// recover non_basic variable 
		GasVar_state[nb_var] = basic_var; // set basic variable	
		e_var = nb_var; // store the eliminate valuable    
		e_row_n = row_n;
		break;
	case 4: // this row already treu
	//	printf("%d:This row is nothing( maybe already true) \n",row_n);
		*j++ = *i;  // store watch list
		if(orig_basic){   // recover
			GasVar_state[ cur_matrixset.nb_rows[row_n] ]  = non_basic_var;
			GasVar_state[ p ]  = basic_var;
		}
		clause_state[row_n/64] |= ((uint64_t)1 << (row_n%64)); // record this clause is already true
		return true;
	case 6:{  // three variable watch , this row cannot find any watch variable in three varaible watch
		//printf("%d:This row is three variable watch \n",row_n);
		*j++ = *i; // stroe watch list
		
		if(   tmp_clause.size() == solver.gaussconfig.add_learn_three  ){
			xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(row_n).is_true();
			add_learn_two(xorEqualFalse,row_n);
			/* xorEqualFalse = cur_matrixset.matrix.getMatrixAt(row_n).is_true();
			for (uint32_t i = 2; i < tmp_clause.size(); i++) {
				assert(!solver.assigns[tmp_clause[i].var()].isUndef());
				const lbool& val= solver.assigns[tmp_clause[i].var() ];
				const bool val_bool = val.getBool();
				xorEqualFalse ^= val_bool;
			}		 */
/* 			const lbool& val= solver.assigns[tmp_clause[2].var() ];
			const bool val_bool = val.getBool();
			if(val_bool) printf("true\n");
			else printf("false\n");
			printf("xorEqualFalse:%d\n",xorEqualFalse); */
			//////////////// first
			if(xorEqualFalse){
				tmp_clause[0] = Lit(tmp_clause[0].var(),false); 
				tmp_clause[1] = Lit(tmp_clause[1].var(),false); 
			}else{
				tmp_clause[0] = Lit(tmp_clause[0].var(),false); 
				tmp_clause[1] = Lit(tmp_clause[1].var(),true); 
			}
			//XorClause* cla = solver.clauseAllocator.XorClause_new(tmp_clause, xorEqualFalse);  // delete for test add learn clause in 4/25
			//Clause* cla = solver.clauseAllocator.Clause_new(tmp_clause, true);
			//Clause* cla  = solver.clauseAllocator.Clause_new(tmp_clause, solver.learnt_clause_group++, true);
			//solver.Gauss_learnts.push(cla); // add for learn clause  			
 			//solver.Gauss_learn_xorclauses.push(cla);
/* 			cla->setGlue(MAX_THEORETICAL_GLUE);
			assert(!(cla->getFreed()));
			assert(solver.assigns[(*cla)[0].var()].isUndef());
			assert(solver.assigns[(*cla)[1].var()].isUndef());
			solver.attachClause(*cla);  */
			//cla->print(); 
			
			/////////// second
			/* if(xorEqualFalse){
				tmp_clause[0] = Lit(tmp_clause[0].var(),true); 
				tmp_clause[1] = Lit(tmp_clause[1].var(),true); 
			}else{
				tmp_clause[0] = Lit(tmp_clause[0].var(),true); 
				tmp_clause[1] = Lit(tmp_clause[1].var(),false); 
			} */
			//Clause* cla2 = solver.clauseAllocator.Clause_new(tmp_clause, true);
/* 			Clause* cla2  = solver.clauseAllocator.Clause_new(tmp_clause, solver.learnt_clause_group++, true);
			//solver.Gauss_learnts.push(cla2); // add for learn clause  			
			cla2->setGlue(MAX_THEORETICAL_GLUE);
			assert(!(cla2->getFreed()));
			solver.attachClause(*cla2);  */
			//cla2->print(); 
		}
		
		//Debug_funtion2(cla); 

		if(!orig_basic)
			return true;
		// basic variable is assign , so need to do gaussian elimination

		
		nb_var = cur_matrixset.nb_rows[row_n] ;  // choose nb variable 
		assert(solver.assigns[nb_var].isUndef());
		assert(GasVar_state[nb_var] == basic_var);
		
		solver.GausWatches[nb_var].clear(); ///clear orignal gausWatch list , because only one basic value in gausWatch list		
		solver.GausWatches[nb_var].push(Solver::GausWatched( row_n ,matrix_no)); // update gausWatch list
		cur_matrixset.nb_rows[row_n] = p; // change to basic and non-basic
		
		e_var = nb_var; // store the eliminate valuable    
		e_row_n = row_n;
		
	
		
		break;
	}
	default:
		assert(false);  // can not here 
		break;
	}
	
/* 	assert(e_var != std::numeric_limits<uint32_t>::max());
	assert(e_row_n != std::numeric_limits<uint16_t>::max());
	assert(orig_basic);
	assert(ret == 5 );
	assert(solver.GausWatches[e_var].size() == 1);
	 */
	do_eliminate = true;
	return true;
}								  



inline void EnhanceGaussian::delete_gausswatch_nonbasic2( const uint16_t  row_n)
{

	bool debug_find = false;
	vec<Solver::GausWatched>&  ws_t  =  solver.GausWatches[ cur_matrixset.nb2_rows[row_n] ];
	
	
	for(int tmpi = ws_t.size() - 1 ; tmpi >= 0 ; tmpi--){
		if(ws_t[tmpi].row_id == row_n){
			ws_t[tmpi] = ws_t.last();
			 ws_t.shrink(1);
			 debug_find = true;
			 break;
		}
	}
	
/* 	if(debug_find == false){
		printf("row_n %d   nb2 %d\n",row_n ,  cur_matrixset.nb2_rows[row_n] );
	} */
	
	assert(debug_find);
	
	
}


void EnhanceGaussian::eliminate_col3(Var e_var  ,uint16_t e_row_n ,Var p,PropBy& confl){

	//cout << "eliminate this column :" << e_var  << " " << p << " " << e_row_n <<  endl;
	//eliminate_num++ ; // undate information
	PackedMatrix::iterator this_row = cur_matrixset.matrix.beginMatrix() + e_row_n;
	PackedMatrix::iterator rowI = cur_matrixset.matrix.beginMatrix();
	PackedMatrix::iterator end = cur_matrixset.matrix.endMatrix(); 
	int ret;
	uint32_t e_col = var_to_col[e_var];
	uint32_t ori_nb = 0 , ori_nb_col = 0;
	uint32_t ori_nb2 = 0 , ori_nb2_col = 0; // orignal non-basic variable 2
	uint32_t nb_var = 0 , nb2_var = 0 ,random_nb = 0;;
	uint32_t num_row = 0;   // row inde
	bool xorEqualFalse = false ;
	bool conflict_bol = false;
	bool conflict_two = false;
	uint32_t conflict_size = UINT_MAX;
	bool eliminate_nb2 = true;
	
	while( rowI != end ){
		if((*rowI)[e_col] &&  this_row !=  rowI ){
			// detect orignal non basic watch list change or not
			ori_nb = cur_matrixset.nb_rows[num_row];
			ori_nb_col = var_to_col[ ori_nb ] ;	
			assert((*rowI)[ori_nb_col]);
			
			// detect orignal non basic 2 watch list change or not
			ori_nb2 = cur_matrixset.nb2_rows[num_row];
			if ( ori_nb2 != std::numeric_limits<uint32_t>::max() ){
				ori_nb2_col = var_to_col[ ori_nb2 ] ;	
				assert((*rowI)[ori_nb2_col]);
			}
			
			(*rowI).xorBoth(*this_row);  // xor eliminate		
			
			// because ori_nb2  may std::numeric_limits<uint32_t>::max()  ; two variable condition
			if ( ori_nb2 != std::numeric_limits<uint32_t>::max() ){
				if (!(*rowI)[ori_nb2_col] )
					eliminate_nb2 = true;
				else
					eliminate_nb2 = false;
			}else	
				eliminate_nb2 = false;
			
			if( !(*rowI)[ori_nb_col]  || eliminate_nb2){  // orignal non basic value is eliminate
				
				if( ori_nb != e_var)   // delelte orignal non basic value in wathc list
					delete_gausswatch(true , num_row);
					
				if(  ori_nb2 != std::numeric_limits<uint32_t>::max()  && ori_nb2 != e_var)   // delelte orignal non basic value in wathc list
					delete_gausswatch_nonbasic2	(num_row);	
				

				ret = (*rowI).propGause_elimination(tmp_clause,solver.assigns,cur_matrixset.col_to_var, GasVar_state ,ori_nb_col, p ,nb_var,nb2_var,random_nb);
					
				//ret = (*rowI).propGause(tmp_clause,solver.assigns,cur_matrixset.col_to_var, GasVar_state ,nb_var , ori_nb_col);
				
				switch(ret){
				case 0:{ // conflict
					//printf("%d:This row is conflict in eliminate col\n",num_row);
					if(tmp_clause.size() >= conflict_size) {
						solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
						cur_matrixset.nb_rows[num_row] = p; // // update in this row non_basic variable
						// for non-basic 2 vairalbe
						assert(random_nb != p && random_nb != e_var );
						if(tmp_clause.size() != 2){  
							assert(random_nb !=  std::numeric_limits<uint32_t>::max() ) ;
							solver.GausWatches[random_nb].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
						}else	
							assert(random_nb ==  std::numeric_limits<uint32_t>::max() ) ;
						
						cur_matrixset.nb2_rows[num_row] = random_nb; // // update in this row non_basic variable
						break;
				    }
					conflict_size = tmp_clause.size()  ;
					if ( conflict_size == 2) {
						//printf("%d:This row is conflict two in eliminate col\n",num_row);
						solver.sum_unit++;
						
						delete_gausswatch(false ,num_row );  
						assert(GasVar_state[tmp_clause[0].var()] ==  basic_var); assert(GasVar_state[tmp_clause[1].var()] ==  non_basic_var); 
						GasVar_state[tmp_clause[0].var()] = non_basic_var; // delete value state;               
						cur_matrixset.nb_rows[num_row] = std::numeric_limits<uint32_t>::max(); // delete non basic value in this row	
						cur_matrixset.nb2_rows[num_row] = std::numeric_limits<uint32_t>::max(); // delete non basic 2 value in this row	
					
						(*rowI).setZero();// reset this row all zero
						
						conflict_twoclause(confl);  // get two conflict  clause						
					
						conflict_two = true;	
					}else{
						solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
						cur_matrixset.nb_rows[num_row] = p; // // update in this row non_basic variable
						// for non-basic 2 vairalbe
						assert(random_nb != p && random_nb != e_var  && random_nb !=  std::numeric_limits<uint32_t>::max());
						solver.GausWatches[random_nb].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
						cur_matrixset.nb2_rows[num_row] = random_nb; // // update in this row non_basic variable
						
						
						xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(num_row).is_true();
						tmp_clause.copyTo(conflict_clause);
					}
					conflict_bol = true;
					break;
				}
				case 2:{
					//printf("%d:This row is propagation in eliminate col\n",num_row);
					if(conflict_bol){  // update no_basic_value
						solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no));
						cur_matrixset.nb_rows[num_row] = p;
						// for non-basic 2 vairalbe
						assert(random_nb != p && random_nb != e_var );
						if(tmp_clause.size() != 2){  
							assert(random_nb !=  std::numeric_limits<uint32_t>::max() ) ;
							solver.GausWatches[random_nb].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
						}else	
							assert(random_nb ==  std::numeric_limits<uint32_t>::max() ) ;
						
						cur_matrixset.nb2_rows[num_row] = random_nb; // // update in this row non_basic variable
						
						break;
					}
					xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(num_row).is_true();
 					if(tmp_clause.size() == 2){
					//	printf("%d:This row is propagation two in eliminate col\n",num_row);
						solver.sum_unit++;
						
						delete_gausswatch(false , num_row);  // delete watch list		
						assert(GasVar_state[tmp_clause[0].var()] ==  basic_var); assert(GasVar_state[tmp_clause[1].var()] ==  non_basic_var); 
						GasVar_state[tmp_clause[0].var()] = non_basic_var; // delete value state;               	
						cur_matrixset.nb_rows[num_row] = std::numeric_limits<uint32_t>::max(); // delete non basic value in this row	
						cur_matrixset.nb2_rows[num_row] = std::numeric_limits<uint32_t>::max();
						(*rowI).setZero();// reset this row all zero
						solver.cancelUntil(0);
						propagation_twoclause(xorEqualFalse); // propagation two clause
					}else{ 
						solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no));// update no_basic information
						cur_matrixset.nb_rows[num_row] = p;
						// for non-basic 2 vairalbe
						assert(random_nb != p && random_nb != e_var  && random_nb !=  std::numeric_limits<uint32_t>::max());
						solver.GausWatches[random_nb].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
						cur_matrixset.nb2_rows[num_row] = random_nb; // // update in this row non_basic variable
						
						
						if (solver.decisionLevel() == 0) {
							solver.uncheckedEnqueue(tmp_clause[0]);
						}else{		
							Clause& cla = *(Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, xorEqualFalse);
							clauses_toclear.push_back(std::make_pair(&cla, solver.trail.size()-1));		
							assert(!(cla.getFreed()));
							assert(solver.assigns[cla[0].var()].isUndef());
							solver.uncheckedEnqueue(cla[0], solver.clauseAllocator.getOffset(&cla));
						}
						// record this clause is already true
						clause_state[num_row/64] |= ((uint64_t)1 << (num_row%64));
					}
				
					break;
				}
				case 5:   // find new watch list
					//printf("%d::This row find new watch list :%d in eliminate col\n",num_row,nb_var);
					assert(nb_var != std::numeric_limits<uint32_t>::max());
					assert(nb2_var != std::numeric_limits<uint32_t>::max());
					assert(nb_var != nb2_var);
					
					solver.GausWatches[nb_var].push(Solver::GausWatched(num_row,matrix_no));// update gausWatch list
					cur_matrixset.nb_rows[num_row] = nb_var;	

					solver.GausWatches[nb2_var].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
					cur_matrixset.nb2_rows[num_row] = nb2_var; // // update in this row non_basic variable
					
					break;
				case 4: // this row already tre
					//printf("%d:This row is nothing( maybe already true) in eliminate col\n",num_row);	
					solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list
					cur_matrixset.nb_rows[num_row] = p;// update in this row non_basic variable
					clause_state[num_row/64] |= ((uint64_t)1 << (num_row%64));// record this clause is already true
					
					assert(random_nb != p && random_nb != e_var );
					if(tmp_clause.size() != 2){  
						assert(random_nb !=  std::numeric_limits<uint32_t>::max() ) ;
						solver.GausWatches[random_nb].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
					}else	
						assert(random_nb ==  std::numeric_limits<uint32_t>::max() ) ;
					
					cur_matrixset.nb2_rows[num_row] = random_nb; // // update in this row non_basic variable
					
					
					break;
				case 6:   
					//printf("%d:This row is 3 variable watch in eliminate col\n",num_row);		
					solver.GausWatches[p].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list
					cur_matrixset.nb_rows[num_row] = p;// update in this row non_basic variable

					if(tmp_clause.size() != 2){  
						//assert(nb_var != p && nb_var != e_var  && nb_var !=  std::numeric_limits<uint32_t>::max());
						solver.GausWatches[nb_var].push(Solver::GausWatched(num_row,matrix_no)); // update gausWatch list 
						cur_matrixset.nb2_rows[num_row] = nb_var; // // update in this row non_basic variable
					}else{
						assert(nb_var ==  std::numeric_limits<uint32_t>::max());
						cur_matrixset.nb2_rows[num_row] = nb_var; // // update in this row non_basic variable
					}
					break;
				default:
					// can not here 
					assert(false);										
						break;
				}
			}
			
		}			
		++rowI;
		num_row++;
	}
	
	if(conflict_bol && !conflict_two ){
		//xorEqualFalse = !cur_matrixset.matrix.getMatrixAt(num_row).is_true();
		Clause* conflPtr = (Clause*)solver.clauseAllocator.XorClause_new(conflict_clause, xorEqualFalse);
		confl = solver.clauseAllocator.getOffset(conflPtr);
		solver.qhead = solver.trail.size();
		solver.Gauseqhead = solver.trail.size();
		
/* 		// Debug conflict clause
		Clause& cla = *conflPtr;
		for (uint32_t ii = 0, size = cla.size(); ii != size; ii++){
			assert(solver.level[cla[ii].var()] <= solver.level[cla[0].var()]);
		}   */ 
	}
	//Debug_funtion();
}



inline void EnhanceGaussian::add_learn_two(const bool xorEqualFalse , uint16_t row_n )
{

	
/* 	printf("%d: ", row_n);
	for(Var i =0 ; i < tmp_clause.size() ; i++){
		printf("%d ", tmp_clause[i].var() );
	}
	printf("%d\n", xorEqualFalse);  */
	
	//solver.restart_num++;
	
    if(solver.assigns[tmp_clause[0].var()] != l_Undef  ||  solver.assigns[tmp_clause[1].var()] != l_Undef)
		return;

	
	
	vec<Var> vars;
	vec<Lit> vars2(tmp_clause.size());
	const bool inverted =  xorEqualFalse;
	for (uint32_t i = 0; i < tmp_clause.size(); i++) {
		vars.push(tmp_clause[i].var());
	}
	
    std::sort(vars.getData(), vars.getDataEnd());
		
	
/* 	printf("sort:");
	for(Var i =0 ; i < vars.size() ; i++){
		printf("%d ", vars[i] );
	}
	printf("\n"); */
	
	///////////////  checke repeat //////////////////
	string key;
	key += itos(vars[0]);
    key += ",";	
	key += itos(vars[1]);
    key += ",";	
	key += itos(vars[2]);

	
	if(solver.clause_map.count(key) > 0) {
		return ;
	}else{
		solver.clause_map.insert( pair<string,bool>(key,true) );
	}
	//cout << "key:"<<key << endl;
	
	/* XorClause* cla = solver.clauseAllocator.XorClause_new(tmp_clause, inverted, solver.learnt_clause_group++);
	solver.Gauss_learnts.push(cla); // add for learn clause  	
	cla->setGlue(MAX_THEORETICAL_GLUE);
    solver.attachClause(*cla); */
	
	vars2[0] = Lit(tmp_clause[0].var(), false ^ inverted);
	vars2[1] = Lit(tmp_clause[1].var(), false ^ inverted);
	vars2[2] = Lit(tmp_clause[2].var(), false ^ inverted);
	Clause* cla = solver.clauseAllocator.Clause_new(vars2, true);
	solver.Gauss_learnts.push(cla); // add for learn clause  			
	cla->setGlue(MAX_THEORETICAL_GLUE);
	solver.attachClause(*cla); 
	
	vars2[0] = Lit(tmp_clause[0].var(), true ^ inverted);
	vars2[1] = Lit(tmp_clause[1].var(), true ^ inverted);
	vars2[2] = Lit(tmp_clause[2].var(), false ^ inverted);
	Clause* cla2 = solver.clauseAllocator.Clause_new(vars2, true);
	solver.Gauss_learnts.push(cla2); // add for learn clause  			
	cla2->setGlue(MAX_THEORETICAL_GLUE);
	solver.attachClause(*cla2); 


	vars2[0] = Lit(tmp_clause[0].var(), true ^ inverted);
	vars2[1] = Lit(tmp_clause[1].var(), false ^ inverted);
	vars2[2] = Lit(tmp_clause[2].var(), true ^ inverted);
	Clause* cla3 = solver.clauseAllocator.Clause_new(vars2, true);
	solver.Gauss_learnts.push(cla3); // add for learn clause  			
	cla3->setGlue(MAX_THEORETICAL_GLUE);
	solver.attachClause(*cla3); 


	vars2[0] = Lit(tmp_clause[0].var(), false ^ inverted);
	vars2[1] = Lit(tmp_clause[1].var(), true ^ inverted);
	vars2[2] = Lit(tmp_clause[2].var(), true ^ inverted);
	Clause* cla4 = solver.clauseAllocator.Clause_new(vars2, true);
	solver.Gauss_learnts.push(cla4); // add for learn clause  			
	cla4->setGlue(MAX_THEORETICAL_GLUE);
	solver.attachClause(*cla4); 
	
}


inline bool EnhanceGaussian::add_detect_three(const bool xorEqualFalse , uint16_t row_n )
{

	
/* 	printf("%d: ", row_n);
	for(Var i =0 ; i < tmp_clause.size() ; i++){
		printf("%d ", tmp_clause[i].var() );
	}
	printf("%d\n", xorEqualFalse);  */
	
	//solver.restart_num++;
	
    if(solver.assigns[tmp_clause[0].var()] != l_Undef  ||  solver.assigns[tmp_clause[1].var()] != l_Undef)
		return false;

	
	
	vec<Var> vars;
	vec<Lit> vars2(tmp_clause.size());
	const bool inverted =  xorEqualFalse;
	for (uint32_t i = 0; i < tmp_clause.size(); i++) {
		vars.push(tmp_clause[i].var());
	}
	
    std::sort(vars.getData(), vars.getDataEnd());
		
	
/* 	printf("sort:");
	for(Var i =0 ; i < vars.size() ; i++){
		printf("%d ", vars[i] );
	}
	printf("\n"); */
	
	///////////////  checke repeat //////////////////
	string key;
	key += itos(vars[0]);
    key += ",";	
	key += itos(vars[1]);
    key += ",";	
	key += itos(vars[2]);

	
	if(solver.clause_map.count(key) > 0) {
		return false;
	}else{
		solver.clause_map.insert( pair<string,bool>(key,true) );
	}
	//cout << "key:"<<key << endl;
	
	/* XorClause* cla = solver.clauseAllocator.XorClause_new(tmp_clause, inverted, solver.learnt_clause_group++);
	solver.Gauss_learnts.push(cla); // add for learn clause  	
	cla->setGlue(MAX_THEORETICAL_GLUE);
    solver.attachClause(*cla); */
	
	vars2[0] = Lit(tmp_clause[0].var(), false ^ inverted);
	vars2[1] = Lit(tmp_clause[1].var(), false ^ inverted);
	vars2[2] = Lit(tmp_clause[2].var(), false ^ inverted);
	Clause* cla = solver.clauseAllocator.Clause_new(vars2, true);
	solver.Gauss_learnts.push(cla); // add for learn clause  			
	cla->setGlue(MAX_THEORETICAL_GLUE);
	solver.attachClause(*cla); 
	
	vars2[0] = Lit(tmp_clause[0].var(), true ^ inverted);
	vars2[1] = Lit(tmp_clause[1].var(), true ^ inverted);
	vars2[2] = Lit(tmp_clause[2].var(), false ^ inverted);
	Clause* cla2 = solver.clauseAllocator.Clause_new(vars2, true);
	solver.Gauss_learnts.push(cla2); // add for learn clause  			
	cla2->setGlue(MAX_THEORETICAL_GLUE);
	solver.attachClause(*cla2); 


	vars2[0] = Lit(tmp_clause[0].var(), true ^ inverted);
	vars2[1] = Lit(tmp_clause[1].var(), false ^ inverted);
	vars2[2] = Lit(tmp_clause[2].var(), true ^ inverted);
	Clause* cla3 = solver.clauseAllocator.Clause_new(vars2, true);
	solver.Gauss_learnts.push(cla3); // add for learn clause  			
	cla3->setGlue(MAX_THEORETICAL_GLUE);
	solver.attachClause(*cla3); 


	vars2[0] = Lit(tmp_clause[0].var(), false ^ inverted);
	vars2[1] = Lit(tmp_clause[1].var(), true ^ inverted);
	vars2[2] = Lit(tmp_clause[2].var(), true ^ inverted);
	Clause* cla4 = solver.clauseAllocator.Clause_new(vars2, true);
	solver.Gauss_learnts.push(cla4); // add for learn clause  			
	cla4->setGlue(MAX_THEORETICAL_GLUE);
	solver.attachClause(*cla4); 
	
	return true;
	
}

void EnhanceGaussian::preprecessing(){
	//printf("~~~~~~~~~~~preprecessing test~~~~~~~~\n");	
	//printf("num_cols:%d , num_rows:%d\n",cur_matrixset.num_cols ,cur_matrixset.num_rows  );
	pre_matrix.getMatrixAt(cur_matrixset.num_rows).setZero();// reset this row all zero
	
	//print_matrix2(pre_matrix);
	//exit(1);
	
	
	uint32_t check_row = 0;
	uint32_t total_find = 0;

	for(uint32_t i =0 ; i < cur_matrixset.num_cols ; i++){
		for (uint32_t j = i + 1 ; j < cur_matrixset.num_cols ; j++){
			PackedMatrix m2 = pre_matrix;
			
			m2.getMatrixAt( cur_matrixset.num_rows ).setZero();// reset this row all zero
			
			m2.getMatrixAt( cur_matrixset.num_rows ).setBit_two(i , j , false);
			//print_matrix2(m2);
			check_row =Detect_two(m2);
			
			
			 if(m2.getMatrixAt(check_row).isZero() && !m2.getMatrixAt(check_row).is_true()){
				//printf()
				//printf("Find %d %d = false \n", cur_matrixset.col_to_var[i]  , cur_matrixset.col_to_var[j] );
				
				tmp_clause.clear();
				tmp_clause.push(Lit( cur_matrixset.col_to_var[i] , true));
				tmp_clause.push(Lit( cur_matrixset.col_to_var[j] , true));
				propagation_twoclause(true);
				
				total_find++;
				continue;
			}
			
			m2 = pre_matrix;
			m2.getMatrixAt( cur_matrixset.num_rows ).setZero();// reset this row all zero
			m2.getMatrixAt( cur_matrixset.num_rows ).setBit_two(i , j , true);
			//print_matrix2(m2);
			
			check_row =Detect_two(m2);
			
			
			 if(m2.getMatrixAt(check_row).isZero() && !m2.getMatrixAt(check_row).is_true()){
				//printf()
				//printf("Find %d %d = true\n", cur_matrixset.col_to_var[i]  , cur_matrixset.col_to_var[j] );
				
				tmp_clause.clear();
				tmp_clause.push(Lit( cur_matrixset.col_to_var[i] , true));
				tmp_clause.push(Lit( cur_matrixset.col_to_var[j] , true));
				propagation_twoclause(false);
				
				total_find++;
			}
		}
	}
	printf("#2xcl:%d\t",total_find);
	//printf("~~~~~~~~~~~preprecessing end~~~~~~~~\n");
}

uint32_t EnhanceGaussian::Detect_two(PackedMatrix &m2){
	uint32_t i = 0;
    uint32_t j = 0;
	
	uint32_t check_row = cur_matrixset.num_rows;
	uint32_t rowid= 0;
	
    PackedMatrix::iterator end = m2.beginMatrix() +cur_matrixset.num_rows + 1 ;
	PackedMatrix::iterator rowIt = m2.beginMatrix();

	while (i != cur_matrixset.num_rows + (uint32_t)1  && j != cur_matrixset.num_cols) {
		PackedMatrix::iterator this_matrix_row = rowIt;
		uint32_t this_matrix_id = rowid;
		
        for (; this_matrix_row != end; ++this_matrix_row) {
            if ((*this_matrix_row)[j])
                break;
			this_matrix_id++;	
        }	
		if (this_matrix_row != end) {
			//swap rows 
            if (this_matrix_row != rowIt) {
                if(this_matrix_id == check_row)
					return check_row;
				else if (rowid == check_row)
					assert(false);
				
				(*rowIt).swapBoth(*this_matrix_row);
				
				/*if(this_matrix_id == check_row)
						check_row = rowid;
				else if (rowid == check_row)
						check_row = this_matrix_id;*/
            }
			// diagnose row
			for (PackedMatrix::iterator k_row = m2.beginMatrix(); k_row != end; ++k_row)  {
                //subtract row i from row u;
                //Now A[u,j] will be 0, since A[u,j] - A[i,j] = A[u,j] -1 = 0.
				if(k_row != rowIt){
					if ((*k_row)[j]){
						(*k_row).xorBoth(*rowIt);
					}
				}
            }
			i++;
            ++rowIt;
			rowid++;
			//printf("basic var:%d\n",m.col_to_var[j] + 1);	
		}
		j++;
	}
	return check_row;
}




void EnhanceGaussian::preprecessing_3(){
	//printf("~~~~~~~~~~~preprecessing test~~~~~~~~\n");	
	//printf("num_cols:%d , num_rows:%d\n",cur_matrixset.num_cols ,cur_matrixset.num_rows  );
	pre_matrix.getMatrixAt(cur_matrixset.num_rows).setZero();// reset this row all zero
	
	//print_matrix2(pre_matrix);
	//exit(1);
	
	
	uint32_t check_row = 0;
	uint32_t total_find = 0;

	for(uint32_t i =0 ; i < cur_matrixset.num_cols ; i++){
		for (uint32_t j = i + 1 ; j < cur_matrixset.num_cols ; j++){
			for (uint32_t k = j + 1 ; k < cur_matrixset.num_cols ; k++){
				PackedMatrix m2 = pre_matrix;
				
				m2.getMatrixAt( cur_matrixset.num_rows ).setZero();// reset this row all zero
				
				m2.getMatrixAt( cur_matrixset.num_rows ).setBit_three(i , j , k ,false);
				//print_matrix2(m2);
				check_row =Detect_two(m2);
				
				
				 if(m2.getMatrixAt(check_row).isZero() && !m2.getMatrixAt(check_row).is_true()){
					//printf()
					//printf("Find %d %d %d = false \n", cur_matrixset.col_to_var[i]  , cur_matrixset.col_to_var[j] ,cur_matrixset.col_to_var[k] );
					
					tmp_clause.clear();
					tmp_clause.push(Lit( cur_matrixset.col_to_var[i] , true));
					tmp_clause.push(Lit( cur_matrixset.col_to_var[j] , true));
					tmp_clause.push(Lit( cur_matrixset.col_to_var[k] , true));
					if(add_detect_three(true, 0))
						total_find++;
					continue;
				}
				
				m2 = pre_matrix;
				m2.getMatrixAt( cur_matrixset.num_rows ).setZero();// reset this row all zero
				m2.getMatrixAt( cur_matrixset.num_rows ).setBit_two(i , j , true);
				//print_matrix2(m2);
				
				check_row =Detect_two(m2);
				
				
				 if(m2.getMatrixAt(check_row).isZero() && !m2.getMatrixAt(check_row).is_true()){
					//printf()
					//printf("Find %d %d %d = true\n", cur_matrixset.col_to_var[i]  , cur_matrixset.col_to_var[j] ,cur_matrixset.col_to_var[k]);
					
					tmp_clause.clear();
					tmp_clause.push(Lit( cur_matrixset.col_to_var[i] , true));
					tmp_clause.push(Lit( cur_matrixset.col_to_var[j] , true));
					tmp_clause.push(Lit( cur_matrixset.col_to_var[k] , true));
					if(add_detect_three(false, 0))
						total_find++;
				}
			}
		}
	}
	printf("#3xcl:%d\t",total_find);
	//printf("~~~~~~~~~~~preprecessing end~~~~~~~~\n");
}




void EnhanceGaussian::reset_stats(){

}

void EnhanceGaussian::EnGauss_final_state()  
{
	printf("DD Informatiion about EnhanceGassian:	%d\n",matrix_no);
	printf("DD adjust_zero:						   	%d\n",adjust_zero);
	printf("DD adjust_one:							%d\n",adjust_one);
	printf("DD adjust_two:							%d\n",adjust_two);
	printf("DD conflict_two:						%d\n",conflict_two);
	printf("DD conflict_n:							%d\n",conflict_n);
	printf("DD propagate_two:						%d\n",propagate_two);
	printf("DD propagate:							%d\n",propagate);
	printf("DD already_true:						%d\n",already_true);
	printf("DD already_true_stop:						%d\n",already_true_stop);
	printf("DD el_conflict_two:						%d\n",el_conflict_two);
	printf("DD el_conflict:							%d\n",el_conflict);
	printf("DD el_propagate:						%d\n",el_propagate);
	printf("DD el_propagate_two:						%d\n",el_propagate_two);
	printf("DD el_already_true:						%d\n",el_already_true);
	printf("DD eliminate_num:						%d\n",eliminate_num);
	printf("DD useful_conflict:						%d\n",useful_conflict);
	printf("DD delete_num_row:						%d\n",delete_num_row);
	printf("DD find_truths_call:						%d\n",find_truths_call);
}


void EnhanceGaussian::print_matrix(matrixset& m) const
{
    uint32_t row = 0;
    for (PackedMatrix::iterator it = m.matrix.beginMatrix(); it != m.matrix.endMatrix(); ++it, row++) {
        cout << *it << " -- row:" << row;
        if (row >= m.num_rows)
            cout << " (considered past the end)";
        cout << endl;
    }
}
void EnhanceGaussian::print_matrix2(PackedMatrix& m) 
{
    uint32_t row = 0;
    for (PackedMatrix::iterator it = m.beginMatrix(); it != m.endMatrix(); ++it, row++) {
        cout << *it << " -- row:" << row;
        cout << endl;
    }
}

void EnhanceGaussian::printf_state(){

/* 	//printf("matrix by EnhanceGaussian::find_truths\n");
	print_matrix(cur_matrixset);
		
	printf("non_basic value in each row:");
	for(size_t i = 0 ; i < cur_matrixset.nb_rows.size() ; i++){
		cout << "(" <<  i <<"," <<  cur_matrixset.nb_rows[i] << ") ";
		assert(   GasVar_sate[cur_matrixset.nb_rows[i]] == non_basic_var );
		
	}
	printf("\n");
	

	
	printf("basic value in each row:");
	for(size_t i = 0 ; i < cur_matrixset.b_rows.size() ; i++){
		assert(   GasVar_sate[cur_matrixset.b_rows[i]] == basic_var );
		cout << "(" << i<<"," <<  cur_matrixset.b_rows[i] << ") ";
	}
	printf("\n");
	
	printf("Watch list:\n");
	for(size_t ii = 0 ; ii < GausWatches.size() ; ii++){
		vec<uint16_t>&  ws_t  =  GausWatches[ii];
		if( ws_t.size() > 0){
			cout << "variable watch " <<  ii  << ":";
			for(size_t jj = 0 ; jj < ws_t.size() ; jj++)
				printf("%d ", ws_t[jj]);
			printf("\n"); 
		}
	} */
	
	//printf("~~~~~~~~EnhanceGaussian:: find_truths end ~~~~~~~~~~~~\n"); 
}

void EnhanceGaussian::Debug_funtion()
{
/* 	printf("\n");
	print_matrix(cur_matrixset);
		
	for(Var i = 0 ; i < row_size.size() ; i++){
		printf("%d:%d\n",i , row_size[i]);
	}
	exit(1); */
/*	
	bool debug_find = false;
	
	
	
	for(size_t i  = 0 ; i <  cur_matrixset.nb2_rows.size() ; i++){
	//	printf("dd:%ld\n", i);
		debug_find = false;
		
		if(std::numeric_limits<uint32_t>::max() == cur_matrixset.nb2_rows[i] )
			continue;
		
		vec<Solver::GausWatched>&  ws_t  =  solver.GausWatches[ cur_matrixset.nb2_rows[i] ];
		for(int tmpi = ws_t.size() - 1 ; tmpi >= 0 ; tmpi--){
			if(ws_t[tmpi].row_id == i){
				ws_t[tmpi] = ws_t.last();
				 debug_find = true;
				 break;
			}
		}
		assert(debug_find);
	}
	
*/	
		
	/* PackedMatrix::iterator this_row = cur_matrixset.matrix.beginMatrix();
	for(uint32_t i = 0 ; i < cur_matrixset.nb_rows.size() ; i++){
		//if(cur_matrixset.b_rows[i] != std::numeric_limits<uint32_t>::max()){
			//assert(  GasVar_sate[cur_matrixset.b_rows[i]] == basic_var );
		//	assert( solver.GausWatches[cur_matrixset.b_rows[i]].size() == 1 );
 			if(!(*this_row)[  var_to_col[cur_matrixset.b_rows[i]]]){
				cout << i << " " << cur_matrixset.b_rows[i] << " " << var_to_col[cur_matrixset.b_rows[i]] <<  endl;
				cout << (*this_row) << endl;
			} 
			//assert((*this_row)[  var_to_col[cur_matrixset.b_rows[i]]]);
		//}
		if(cur_matrixset.nb_rows[i] != std::numeric_limits<uint32_t>::max()){
			//assert( GasVar_sate[cur_matrixset.nb_rows[i]] == non_basic_var );
			if(solver.GausWatches[cur_matrixset.nb_rows[i]].size() <= 0 ){
				printf("DD %d %d\n",cur_matrixset.nb_rows[i] , i);
			}
			assert( solver.GausWatches[cur_matrixset.nb_rows[i]].size() > 0 );
			assert((*this_row)[  var_to_col[cur_matrixset.nb_rows[i]]]);
		}
		++this_row;
		//cout << "Debug : "<<*(cur_matrixset.nbAdrress[i]) << " " <<  i  << " " << cur_matrixset.nb_rows[i]<< endl;
		if( *(cur_matrixset.nbAdrress[i]) != i){
			cout << "Debug : "<<*(cur_matrixset.nbAdrress[i]) << " " <<  i  << " " << cur_matrixset.nb_rows[i]<< endl;
			dd =true;
		}
		//	printf_state();
		//assert(  *(cur_matrixset.nbAdrress[i]) == i );
	}	
	//assert(dd == false);
	
	for (int i = clauses_toclear.size()-1; i >= 0 ; i--) {
		//solver.clauseAllocator.clauseFree(clauses_toclear[i].first);
		   assert(!(clauses_toclear[i].first)->getFreed());
    }  */
	
}


void EnhanceGaussian::test(){
	printf("~~~~~~~~~~~EnhanceGaussian test~~~~~~~~\n");	
	print_matrix(cur_matrixset);
	printf("~~~~~~~~~~~EnhanceGaussian end~~~~~~~~\n");
}


