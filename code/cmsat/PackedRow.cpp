/***********************************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
**************************************************************************************************/

#include "cmsat/PackedRow.h"

using namespace CMSat;

bool PackedRow::operator ==(const PackedRow& b) const
{
    #ifdef DEBUG_ROW
    assert(size > 0);
    assert(b.size > 0);
    assert(size == b.size);
    #endif

    return (std::equal(b.mp-1, b.mp+size, mp-1));
}

bool PackedRow::operator !=(const PackedRow& b) const
{
    #ifdef DEBUG_ROW
    assert(size > 0);
    assert(b.size > 0);
    assert(size == b.size);
    #endif

    return (!std::equal(b.mp-1, b.mp+size, mp-1));
}

uint32_t PackedRow::popcnt() const
{
    uint32_t popcnt = 0;
    for (uint32_t i = 0; i < size; i++) if (mp[i]) { 
        uint64_t tmp = mp[i];
        for (uint32_t i2 = 0; i2 < 64; i2++) {
            popcnt += (tmp & 1);
            tmp >>= 1;
        }
    }
    return popcnt;
}


uint32_t PackedRow::popcnt(const uint32_t from) const
{
    uint32_t popcnt = 0;
    for (uint32_t i = from/64; i != size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        uint32_t i2;
        if (i == from/64) {
            i2 = from%64;
            tmp >>= i2;
        } else
            i2 = 0;
        for (; i2 < 64; i2++) {
            popcnt += (tmp & 1);
            tmp >>= 1;
        }
    }
    return popcnt;
}

const bool PackedRow::fill(vec<Lit>& tmp_clause, const vec<lbool>& assigns, const vector<Var>& col_to_var_original) const
{
    bool final = !is_true_internal;

    tmp_clause.clear();
    uint32_t col = 0;
    bool wasundef = false; 
    for (uint32_t i = 0; i < size; i++) for (uint32_t i2 = 0; i2 < 64; i2++) { 
        if ((mp[i] >> i2) &1) {
            const Var& var = col_to_var_original[col];
            assert(var != std::numeric_limits<Var>::max());

            const lbool val = assigns[var];
            const bool val_bool = val.getBool();
            tmp_clause.push(Lit(var, val_bool));
            final ^= val_bool;
            if (val.isUndef()) {
                assert(!wasundef);
                Lit tmp(tmp_clause[0]);
                tmp_clause[0] = tmp_clause.last();
                tmp_clause.last() = tmp;
                wasundef = true;
            }
        }
        col++;
    }
    if (wasundef) {
        tmp_clause[0] ^= final;
        //assert(ps != ps_first+1);
    } else
        assert(!final);

    return wasundef;
}


uint32_t PackedRow::find_watchVar(vec<Lit>& tmp_clause, const vector<Var>& col_to_var,vec<bool> &GasVar_state , uint32_t& nb_var )
{
	uint32_t  tmp_var = 0;
	uint32_t popcnt = 0;
	nb_var = std::numeric_limits<uint32_t>::max();
	uint32_t i;
	tmp_clause.clear();
	
	
	for(i = 0; i < size*64; i++) {
		if (this->operator[](i)){
			popcnt++;
			tmp_var = col_to_var[i];
			tmp_clause.push(Lit(tmp_var, false));
			if( !GasVar_state[tmp_var] ){  //nobasic 
				nb_var = tmp_var;
				break;
			}else{  // basic
				Lit tmp(tmp_clause[0]);
				tmp_clause[0] = tmp_clause.last();
				tmp_clause.last() = tmp;	
			}
		}
	}
	
	for( i = i + 1 ; i <  size*64; i++) {
		if (this->operator[](i)){
			popcnt++;
			tmp_var = col_to_var[i];
			tmp_clause.push(Lit(tmp_var, false));
			if( GasVar_state[tmp_var] ){  //basic 
				Lit tmp(tmp_clause[0]);
				tmp_clause[0] = tmp_clause.last();
				tmp_clause.last() = tmp;
			}
		}
	}
	assert(tmp_clause.size() == popcnt);
	assert( popcnt == 0 || GasVar_state[ tmp_clause[0].var() ]) ;
	return popcnt;

}
// add by hankf4
uint32_t PackedRow::find_watchVar_2(vec<Lit>& tmp_clause, const vector<Var>& col_to_var,vec<bool> &GasVar_state , uint32_t& nb_var, uint32_t& nb_var2 )
{
	uint32_t  tmp_var = 0;
	uint32_t popcnt = 0;
	nb_var = std::numeric_limits<uint32_t>::max();
	nb_var2 = std::numeric_limits<uint32_t>::max();
	uint32_t i;
	tmp_clause.clear();
	
	
	for(i = 0; i < size*64; i++) {
		if (this->operator[](i)){
			popcnt++;
			tmp_var = col_to_var[i];
			tmp_clause.push(Lit(tmp_var, false));
			if( !GasVar_state[tmp_var] ){  //nobasic 
				nb_var = tmp_var;
				break;
			}else{  // basic
				Lit tmp(tmp_clause[0]);
				tmp_clause[0] = tmp_clause.last();
				tmp_clause.last() = tmp;	
			}
		}
	}
	
	for( i = i + 1 ; i <  size*64; i++) {
		if (this->operator[](i)){
			popcnt++;
			tmp_var = col_to_var[i];
			tmp_clause.push(Lit(tmp_var, false));
			if( !GasVar_state[tmp_var] ){  //nobasic 2
				nb_var2 = tmp_var;
				break;
			}else{  // basic
				Lit tmp(tmp_clause[0]);
				tmp_clause[0] = tmp_clause.last();
				tmp_clause.last() = tmp;	
			}
		}
	}

	
	for( i = i + 1 ; i <  size*64; i++) {
		if (this->operator[](i)){
			popcnt++;
			tmp_var = col_to_var[i];
			tmp_clause.push(Lit(tmp_var, false));
			if( GasVar_state[tmp_var] ){  //basic 
				Lit tmp(tmp_clause[0]);
				tmp_clause[0] = tmp_clause.last();
				tmp_clause.last() = tmp;
			}
		}
	}

	assert(tmp_clause.size() == popcnt);
	assert( popcnt == 0 || GasVar_state[ tmp_clause[0].var() ]) ;
	return popcnt;

}


int PackedRow::propGause(vec<Lit>& tmp_clause,const vec<lbool>& assigns, const vector<Var>& col_to_var, vec<bool> &GasVar_state ,uint32_t& nb_var , uint32_t start)
{

	bool final = !is_true_internal;
	nb_var = std::numeric_limits<uint32_t>::max();
	tmp_clause.clear();
	
	for ( uint32_t i = start/64; i != size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        uint32_t i2;
        for (i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
				const Var& var = col_to_var[ i * 64  + i2];
				const lbool& val= assigns[var];
				if (val.isUndef() &&  !GasVar_state[var] ){  // find non basic value
					nb_var = var;
					return 5;   // nothing
				}
				const bool val_bool = val.getBool();
				final ^= val_bool;
				tmp_clause.push(Lit(var, val_bool));
				if ( GasVar_state[var] ) {
					Lit tmp_lit(tmp_clause[0]);
					tmp_clause[0] = tmp_clause.last();
					tmp_clause.last() = tmp_lit;
				}
			}
            tmp >>= 1;
        }
    }
	for ( uint32_t i =0; i != start/64; i++) if (mp[i]) {
        uint64_t tmp = mp[i]; 
        uint32_t i2;
        for (i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
				const Var& var = col_to_var[ i * 64  + i2];
				const lbool& val= assigns[var];
				if (val.isUndef() &&  !GasVar_state[var] ){  // find non basic value
					nb_var = var;
					return 5;   // nothing
				}
				const bool val_bool = val.getBool();
				final ^= val_bool;
				tmp_clause.push(Lit(var, val_bool));
				if ( GasVar_state[var] ) {
					Lit tmp_lit(tmp_clause[0]);
					tmp_clause[0] = tmp_clause.last();
					tmp_clause.last() = tmp_lit;
				}
			}
            tmp >>= 1;
        }
    }
/*     uint32_t popcnt = 0;
    for (uint32_t i = 0; i < size; i++) if (mp[i]) { 
        uint64_t tmp = mp[i];
        for (uint32_t i2 = 0; i2 < 64; i2++) {
            popcnt += (tmp & 1);
            tmp >>= 1;
        }
    }
	assert(popcnt == tmp_clause.size()); */
	
	
	if (assigns[tmp_clause[0].var()].isUndef()) {    // propogate
		tmp_clause[0] = tmp_clause[0].unsign()^final;
		return 2;  // propogate
    } else if (!final) {
		return 0;  // conflict
    }
	// this row already true
	return 4;  // nothing
		
}

int PackedRow::propGause_add_learnt_two(vec<Lit>& tmp_clause,const vec<lbool>& assigns, const vector<Var>& col_to_var, vec<bool> &GasVar_state ,uint32_t& nb_var , uint32_t start, uint32_t& row_size)
{

	bool final = !is_true_internal;
	nb_var = std::numeric_limits<uint32_t>::max();
	tmp_clause.clear();
	row_size = 0;
	bool nothing = false;
	
	for ( uint32_t i = start/64; i != size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        uint32_t i2;
        for (i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
			
				// add for knowing size
				row_size++;

				
				const Var& var = col_to_var[ i * 64  + i2];
				const lbool& val= assigns[var];
				if (!nothing &&  val.isUndef() &&  !GasVar_state[var] ){  // find non basic value
					nb_var = var;
					nothing = true;
					//return 5;   // nothing
				}
				const bool val_bool = val.getBool();
				final ^= val_bool;
				tmp_clause.push(Lit(var, val_bool));
				if ( GasVar_state[var] ) {
					Lit tmp_lit(tmp_clause[0]);
					tmp_clause[0] = tmp_clause.last();
					tmp_clause.last() = tmp_lit;
				}
			}
            tmp >>= 1;
        }
    }
	for ( uint32_t i =0; i != start/64; i++) if (mp[i]) {
        uint64_t tmp = mp[i]; 
        uint32_t i2;
        for (i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
				
				// add for knowing size
				row_size++;
			
				const Var& var = col_to_var[ i * 64  + i2];
				const lbool& val= assigns[var];
				if (!nothing && val.isUndef() &&  !GasVar_state[var] ){  // find non basic value
					nb_var = var;
					nothing = true;
					//continue;
					//return 5;   // nothing
				}
				const bool val_bool = val.getBool();
				final ^= val_bool;
				tmp_clause.push(Lit(var, val_bool));
				if ( GasVar_state[var] ) {
					Lit tmp_lit(tmp_clause[0]);
					tmp_clause[0] = tmp_clause.last();
					tmp_clause.last() = tmp_lit;
				}
			}
            tmp >>= 1;
        }
    }
/*     uint32_t popcnt = 0;
    for (uint32_t i = 0; i < size; i++) if (mp[i]) { 
        uint64_t tmp = mp[i];
        for (uint32_t i2 = 0; i2 < 64; i2++) {
            popcnt += (tmp & 1);
            tmp >>= 1;
        }
    }
	assert(popcnt == tmp_clause.size()); */
	
	if(nothing) {
		assert(tmp_clause.size() == row_size);
		return 5;   // nothing
	}
	if (assigns[tmp_clause[0].var()].isUndef()) {    // propogate
		tmp_clause[0] = tmp_clause[0].unsign()^final;
		return 2;  // propogate
    } else if (!final) {
		return 0;  // conflict
    }
	// this row already true
	return 4;  // nothing
		
}


int PackedRow::propGause2(vec<Lit>& tmp_clause,const vec<lbool>& assigns, const vector<Var>& col_to_var, vec<bool> &GasVar_state ,uint32_t& nb_var ,const uint32_t start , const uint32_t nb_var2 ){
	bool final = !is_true_internal;
	nb_var = std::numeric_limits<uint32_t>::max();
	tmp_clause.clear();
	uint32_t nb2_var_location =  std::numeric_limits<uint32_t>::max();
	
	//vector<Var> change_clause;
	//assert(nb_var2 != std::numeric_limits<uint32_t>::max());
	
	for ( uint32_t i = start/64; i != size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        uint32_t i2;
        for (i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
				const Var& var = col_to_var[ i * 64  + i2];
				const lbool& val= assigns[var];
				if (val.isUndef() &&  !GasVar_state[var]  && var != nb_var2){  // find non basic value
					nb_var = var;
					return 5;   // nothing
				}
				
				if (var == nb_var2)
					nb2_var_location = tmp_clause.size();
				
				const bool val_bool = val.getBool();
				final ^= val_bool;
				tmp_clause.push(Lit(var, val_bool));
				if ( GasVar_state[var] ) {
					Lit tmp_lit(tmp_clause[0]);
					tmp_clause[0] = tmp_clause.last();
					tmp_clause.last() = tmp_lit;
					
					if(tmp_lit.var() == nb_var2)
						nb2_var_location = tmp_clause.size()-1;
				}
			}
            tmp >>= 1;
        }
    }
	for ( uint32_t i =0; i != start/64; i++) if (mp[i]) {
        uint64_t tmp = mp[i]; 
        uint32_t i2;
        for (i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
				const Var& var = col_to_var[ i * 64  + i2];
				const lbool& val= assigns[var];
				if (val.isUndef() &&  !GasVar_state[var]   && var != nb_var2 ){  // find non basic value
					nb_var = var;
					return 5;   // nothing
				}
				
				if (var == nb_var2)
					nb2_var_location = tmp_clause.size();
				
				const bool val_bool = val.getBool();
				final ^= val_bool;
				tmp_clause.push(Lit(var, val_bool));
				if ( GasVar_state[var] ) {
					Lit tmp_lit(tmp_clause[0]);
					tmp_clause[0] = tmp_clause.last();
					tmp_clause.last() = tmp_lit;
					
					if(tmp_lit.var() == nb_var2)
						nb2_var_location = tmp_clause.size()-1;
				}
			}
            tmp >>= 1;
        }
    }
	
	
/*     uint32_t popcnt = 0;
    for (uint32_t i = 0; i < size; i++) if (mp[i]) { 
        uint64_t tmp = mp[i];
        for (uint32_t i2 = 0; i2 < 64; i2++) {
            popcnt += (tmp & 1);
            tmp >>= 1;
        }
    }
	assert(popcnt == tmp_clause.size()); */
/* 	if(tmp_clause.size() == 0)
		return 10; */
	
	
	if(nb_var2 == std::numeric_limits<uint32_t>::max()){   // only two variable
		assert(tmp_clause.size() == 2);
		if (assigns[tmp_clause[0].var()].isUndef()) {    // propogate
			tmp_clause[0] = tmp_clause[0].unsign()^final;
			return 2;  // propogate
		} else if (!final) {
			return 0;  // conflict
		}
		// this row already true
		return 4;  // nothing
	}
	

	const lbool& val= assigns[nb_var2]; 
	
	if(val.isUndef() && assigns[tmp_clause[0].var()].isUndef() ){  // 3-watch clause
		//if(tmp_clause.size() > 3){
		//	return 6;
		//}
		assert(nb2_var_location !=  std::numeric_limits<uint32_t>::max());
		//assert(tmp_clause.size() == 3);
		
		Lit tmp_lit(tmp_clause[1]);
		tmp_clause[1] = tmp_clause[nb2_var_location];
		tmp_clause[nb2_var_location] = tmp_lit;
		
		/*
		if(!(assigns[tmp_clause[0].var()].isUndef()  && assigns[tmp_clause[1].var()].isUndef() )){
			Lit tmp_lit2(tmp_clause[1]);
			printf("DD: %d %d %d\n", nb_var2 , tmp_lit2.var(),nb2_var_location);
			assert(0);
		}*/
		
		return 6;
	}else if (val.isUndef()){   // non-basic2 variable propagate
		assert(!(assigns[tmp_clause[0].var()].isUndef()));
		
		Lit tmp_lit(tmp_clause[0]);
		tmp_clause[0] = tmp_clause[nb2_var_location];
		tmp_clause[nb2_var_location] = tmp_lit;
		
		tmp_clause[0] = tmp_clause[0].unsign()^final;
		return 2; // propogate
		
	}else if (assigns[tmp_clause[0].var()].isUndef()) {    // basic variable propogate
		assert(!(val.isUndef()));
		tmp_clause[0] = tmp_clause[0].unsign()^final;
		return 2;  // propogate
    } else if (!final) {
		return 0;  // conflict
    }
	// this row already true
	return 4;  // nothing
}

int PackedRow::propGause_elimination(vec<Lit>& tmp_clause,const vec<lbool>& assigns, const vector<Var>& col_to_var, vec<bool> &GasVar_state ,const uint32_t start, const uint32_t p , uint32_t& nb_var ,uint32_t& nb_var2 , uint32_t& random_nb  ){
	bool final = !is_true_internal;
	uint32_t num_nb_2 = 0;
	
	
	nb_var = std::numeric_limits<uint32_t>::max();
	nb_var2 = std::numeric_limits<uint32_t>::max();
	random_nb = std::numeric_limits<uint32_t>::max();
	tmp_clause.clear();
	
	for ( uint32_t i = start/64; i != size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        uint32_t i2;
        for (i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
				const Var& var = col_to_var[ i * 64  + i2];
				const lbool& val= assigns[var];
				if (val.isUndef() &&  !GasVar_state[var]){  // find non basic value
					if(num_nb_2 == 0){
						nb_var = var;
						num_nb_2 = 1;
					}
					else if(num_nb_2 == 1){
						nb_var2 = var;
						num_nb_2 = 2;
					}
						
					if(num_nb_2 == 2)	
						return 5;   // nothing
					assert(num_nb_2 < 2);
				}
				if(var !=  p && !GasVar_state[var])
					random_nb = var;
				
				const bool val_bool = val.getBool();
				final ^= val_bool;
				tmp_clause.push(Lit(var, val_bool));
				if ( GasVar_state[var] ) {
					Lit tmp_lit(tmp_clause[0]);
					tmp_clause[0] = tmp_clause.last();
					tmp_clause.last() = tmp_lit;
				}
			}
            tmp >>= 1;
        }
    }
	for ( uint32_t i =0; i != start/64; i++) if (mp[i]) {
        uint64_t tmp = mp[i]; 
        uint32_t i2;
        for (i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
				const Var& var = col_to_var[ i * 64  + i2];
				const lbool& val= assigns[var];
				if (val.isUndef() &&  !GasVar_state[var]){  // find non basic value
					if(num_nb_2 == 0){
						nb_var = var;
						num_nb_2 = 1;
					}
					else if(num_nb_2 == 1){
						nb_var2 = var;
						num_nb_2 = 2;
					}
						
					if(num_nb_2 == 2)	
						return 5;   // nothing
					assert(num_nb_2 < 2);
				}	
				if(var !=  p && !GasVar_state[var])
					random_nb = var;
				
				const bool val_bool = val.getBool();
				final ^= val_bool;
				tmp_clause.push(Lit(var, val_bool));
				if ( GasVar_state[var] ) {
					Lit tmp_lit(tmp_clause[0]);
					tmp_clause[0] = tmp_clause.last();
					tmp_clause.last() = tmp_lit;
				}
			}
            tmp >>= 1;
        }
    }
	
	if(num_nb_2 == 1){
		// because if any backtract , woluld cause  p == nb-var ,  avoid !!!!!
		if(p == nb_var){
			nb_var = random_nb ;
		}
		return 6;
	}else if(num_nb_2 == 0){
		if (assigns[tmp_clause[0].var()].isUndef()) {    // propogate
			tmp_clause[0] = tmp_clause[0].unsign()^final;
			return 2;  // propogate
		} else if (!final) {
			return 0;  // conflict
		}
		// this row already true
		return 4;  // nothing
	}else {
		assert(0);
	}

	return 4;  // nothing

}



