#ifndef ENHANCEGAUSSIAN_H
#define ENHANCEGAUSSIAN_H

#include <vector>
#include <limits>
#include <string>
#include <utility>
#include <map>
#include<sstream>

#ifdef _MSC_VER
#include <msvc/stdint.h>  
#else
#include <stdint.h>
#endif //_MSC_VER

#include "cmsat/SolverTypes.h"
#include "cmsat/Solver.h"
#include "cmsat/GaussianConfig.h" 
#include "cmsat/PackedMatrix.h"
#include "cmsat/BitArray.h"

//#define VERBOSE_DEBUG
//#define DEBUG_GAUSS
#define basic_var true
#define non_basic_var false 

namespace CMSat {

using std::string;
using std::pair;
using std::vector;
using std::stringstream ;

class Clause;


class EnhanceGaussian {

protected:
	// variable 
    Solver& solver;   // orignal sat solver
    const GaussConf& config;
    const uint matrix_no;			// matrix index
   
	bool disabled; // Gauss is disabled
	
	vec<Lit> tmp_clause;  // conflict&propagation handling
	vec<Lit> conflict_clause;  // conflict&propagation handling
	vec<Lit> prpagation_lit ;  // propagation lit
	//vec<bool> row_three; // each row size;
	//map<string,bool> clause_map;
	// gaussian state     0         1              2            3                4
	enum gaussian_ret {conflict, unit_conflict, propagation, unit_propagation, nothing};
	
	// some information state
	uint32_t            adjust_zero; 
	uint32_t            adjust_one;
	uint32_t            adjust_two;
	uint32_t            conflict_two;
	uint32_t            conflict_n;
	uint32_t            propagate_two;
	uint32_t            propagate;
	uint32_t            already_true;
	uint32_t            already_true_stop;
	uint32_t            el_conflict_two;
	uint32_t            el_conflict;
	uint32_t            el_propagate_two;
	uint32_t            el_propagate;
	uint32_t            el_already_true;
	uint32_t            eliminate_num;
	uint32_t            useful_conflict;
	uint32_t            delete_num_row;
	uint32_t			find_truths_call;
	uint32_t 			called;
	
	// variable added by hankf4 ///////////////////////////////
	vec<bool> 			GasVar_state ;  	// variable state 
	vector<Var> 		var_to_col;         	// variable to column
    PackedMatrix pre_matrix; // The matrix is used in preprocessor
   ///////////////////////////////////////////////////////////
    class matrixset
    {
    public:
		// added by hankf4
		vec<Var> nb_rows; // the non_basic value in each row
		vec<Var> nb2_rows; // the non_basic2  value in each row for test three-value watch literal.
		//vec<Var> b_rows; // the basic value in each row
		
		// used in orignal matrix
        PackedMatrix matrix; // The matrix, updated to reflect variable assignements
        vector<Var> col_to_var; // col_to_var[COL] tells which variable is at a given column in the matrix. Gives unassigned_var if the COL has been zeroed (i.e. the variable assigned)
        uint16_t num_rows; // number of active rows in the matrix. Unactive rows are rows that contain only zeros (and if they are conflicting, then the conflict has been treated)
        uint32_t num_cols; // number of active columns in the matrix. The columns at the end that have all be zeroed are no longer active
    };

    //Saved states
   // vector<matrixset> matrix_sets; // The matrixsets for depths 'decision_from' + 0,  'decision_from' + only_nth_gaussian_save, 'decision_from' + 2*only_nth_gaussian_save, ... 'decision_from' + 'decision_until'.
    matrixset cur_matrixset; // The current matrixset, i.e. the one we are working on, or the last one we worked on
	
	// function
	//void init(); // Initalise gauss state
    void fill_matrix(matrixset& origMat); // Fills the origMat matrix
	uint32_t select_columnorder(vector<Var>& var_to_col,matrixset& origMat); // Fills var_to_col and col_to_var of the origMat matrix.
	void print_matrix(matrixset& m) const ; // print matrix
	void print_matrix2(PackedMatrix& m) ; // print matrix
	void printf_state();
	
	void preprecessing();
	uint32_t Detect_two(PackedMatrix &m2);
	
	void preprecessing_3();
	inline bool add_detect_three(const bool xorEqualFalse , uint16_t row_n );
	//uint32_t Detect_three(PackedMatrix &m2);
	// main gaussian function
	void eliminate(matrixset& matrix); //does the actual gaussian elimination
	//add by hankf4
	gaussian_ret adjust_matrix(matrixset& matrix); // adjust matrix, include watch, check row is zero, etc.
	inline void delete_gausswatch(const bool orig_basic , const uint16_t  row_n);
	inline void conflict_twoclause(PropBy& confl);
	inline void propagation_twoclause(const bool xorEqualFalse);
	inline void delete_gausswatch_nonbasic2( const uint16_t  row_n);
	inline void add_learn_two(const bool xorEqualFalse ,  uint16_t row_n );  // add learn clause
	
public:
	// variable
	vector <XorClause* > xorclauses;   // xorclauses
	vector<pair<Clause*, uint32_t> > clauses_toclear; // use to delete propagate clause
	vector<pair<uint16_t, uint32_t> > clause_state_toclear; // use to delete this clause is already true when backtrack
	uint64_t*  clause_state; // use to recorde this clause is already true
	uint32_t clause_state_size;
	// constrcut
	EnhanceGaussian(Solver& solver, const GaussConf& config, const uint32_t matrix_no, const vector<XorClause*>& xorclauses);
    ~EnhanceGaussian();
	
	// functiion
	const bool full_init();  // initial arrary
	/*****************************  main algorithm ***********************************/
	bool  find_truths(const vec<Solver::GausWatched>::iterator &i, vec<Solver::GausWatched>::iterator &j,Var p ,PropBy& confl, const uint16_t row_n , bool &do_eliminate , Var &e_var , uint16_t &e_row_n);  //execute gaussian
	void eliminate_col(Var e_var  ,uint16_t e_row_n ,Var p,PropBy& confl); // when basic variable is touch , eliminate one col ;
	/********************************************************************************/	
	/*************************** three variable watch algorithm *******************************/
	bool  find_truths3(const vec<Solver::GausWatched>::iterator &i, vec<Solver::GausWatched>::iterator &j,Var p ,PropBy& confl, const uint16_t row_n , bool &do_eliminate , Var &e_var , uint16_t &e_row_n);  //execute gaussian
	void eliminate_col3(Var e_var  ,uint16_t e_row_n ,Var p,PropBy& confl); // when basic variable is touch , eliminate one col ;
	/* void eliminate_col3(Var e_var  ,uint16_t e_row_n ,Var p,PropBy& confl , 
					   int &ret_gauss ,  vec<Lit>& conflict_clause_gauss ,uint32_t& conflict_size_gauss,bool &xorEqualFalse_gauss); // when basic variable is touch , eliminate one col ; 
 */	/*******************************************************************************/
	
	
	//void update_nbaddress(vec<Solver::GausWatched>::iterator &j,uint16_t row_n , Var p);
	//void delete_nbaddress(vec<Solver::GausWatched>::iterator &update_address ,uint16_t update_row , Var ori_nb );
	//void gaussian();  // gaussian algorithm
	void canceling(const uint32_t sublevel); //functions used throughout the Solver
	void test();  // debug
	void EnGauss_final_state();  // print final EnGauss information	
	void Debug_funtion(); // used to debug orz.......
	bool should_check_gauss();
	void reset_stats();
	
	uint32_t check_assignment();
	void reset_gather();
	void chekc_gather();
	
	const uint32_t enget_called() const;
    const uint32_t enget_useful_prop() const;
    const uint32_t enget_useful_confl() const;
	const uint32_t enget_useful_prop_two() const;
    const uint32_t enget_useful_confl_two() const;
	const uint32_t enget_eliminate_num() const;
	const uint32_t enget_el_conflict_two() const;
	const uint32_t enget_el_conflict() const;
	const uint32_t enget_el_propagate_two() const;
	const uint32_t enget_el_propagate() const;
	const uint32_t enget_alreadytrue() const;
	const uint32_t enget_el_enget_alreadytrue() const;
	const uint32_t enget_already_true_stop() const;
	
	string itos(int n);
};

inline uint32_t EnhanceGaussian::check_assignment(){
	uint32_t assign_sum = 0;
	for(size_t i = 0 ; i< cur_matrixset.num_cols ; i++){
		const Var& var = cur_matrixset.col_to_var[i];
		if(!(solver.assigns[var].isUndef()))
			assign_sum++;
	}
	
	return (uint32_t)((double)assign_sum / cur_matrixset.num_cols * 100);
	
}

inline void EnhanceGaussian::reset_gather(){
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
	find_truths_call = 0;
}
inline void EnhanceGaussian::chekc_gather(){
	uint32_t total = conflict_two+conflict_n + el_conflict_two + el_conflict + propagate_two+propagate + el_propagate+el_propagate_two + already_true+el_already_true;
	printf("%d\t%d\t%f\t%d\t%d\n"
			,conflict_two+conflict_n + el_conflict_two + el_conflict
			,propagate_two+propagate + el_propagate+el_propagate_two
			, (double)(conflict_two+conflict_n + el_conflict_two + el_conflict + propagate_two+propagate + el_propagate+el_propagate_two) / total * 100
			,eliminate_num 
			,find_truths_call );
}


inline bool EnhanceGaussian::should_check_gauss()
{
	 return !disabled ;
}


inline const uint32_t EnhanceGaussian::enget_called() const
{
    return find_truths_call;
}

inline const uint32_t EnhanceGaussian::enget_useful_prop() const
{
    return  propagate;
}

inline const uint32_t EnhanceGaussian::enget_useful_confl() const
{
    return conflict_n;
}
inline const uint32_t EnhanceGaussian::enget_useful_prop_two() const
{
    return propagate_two;
}
inline const uint32_t EnhanceGaussian::enget_useful_confl_two() const
{
    return  conflict_two;
}
inline const uint32_t EnhanceGaussian::enget_eliminate_num() const
{
    return eliminate_num;
}

inline	const uint32_t EnhanceGaussian::enget_el_conflict_two() const{
	 return el_conflict_two;
}
inline	const uint32_t EnhanceGaussian::enget_el_conflict() const{
	 return el_conflict;
}
inline	const uint32_t EnhanceGaussian::enget_el_propagate_two() const{
	 return el_propagate_two;
}
inline	const uint32_t EnhanceGaussian::enget_el_propagate() const{
	 return el_propagate;
}

inline	const uint32_t EnhanceGaussian::enget_alreadytrue() const{
	 return already_true;
}
inline	const uint32_t EnhanceGaussian::enget_el_enget_alreadytrue() const{
	 return el_already_true;
}
inline	const uint32_t EnhanceGaussian::enget_already_true_stop() const{
	 return already_true_stop;
}

inline string EnhanceGaussian::itos(int n) {
	stringstream ss;
	ss << n;
	return ss.str();
}




}


#endif //ENHANCEGAUSSIAN_H
