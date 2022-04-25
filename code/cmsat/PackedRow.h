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

#ifndef PACKEDROW_H
#define PACKEDROW_H

//#define DEBUG_ROW

#include <vector>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "cmsat/SolverTypes.h"
#include "cmsat/Vec.h"
#include <string.h>
#include <iostream>
#include <algorithm>
#include <limits>


namespace CMSat {

using std::vector;
using std::cout;

class PackedMatrix;

class PackedRow
{
public:
    bool operator ==(const PackedRow& b) const;
    bool operator !=(const PackedRow& b) const;

    PackedRow& operator=(const PackedRow& b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(size == b.size);
        #endif

        memcpy(mp-1, b.mp-1, size+1);
        return *this;
    }

    PackedRow& operator^=(const PackedRow& b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        for (uint32_t i = 0; i != size; i++) {
            *(mp + i) ^= *(b.mp + i);
        }

        is_true_internal ^= b.is_true_internal;
        return *this;
    }

    void xorBoth(const PackedRow& b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif
		/*
        for (uint32_t i = 0; i != 2*size+1; i++) {
            *(mp + i) ^= *(b.mp + i);
        }*/
        for (uint32_t i = 0; i != size; i++) {
            *(mp + i) ^= *(b.mp + i);
        }

        is_true_internal ^= b.is_true_internal;
    }


    uint32_t popcnt() const;
    uint32_t popcnt(uint32_t from) const;

    bool popcnt_is_one() const
    {
        #if __GNUC__ >= 4
        int ret = 0;
        for (uint32_t i = 0; i != size; i++) {
            ret += __builtin_popcount(mp[i]&0xffffffff);
            ret += __builtin_popcount(mp[i]>>32);
            if (ret > 1) return false;
        }
        return ret == 1;
        #else
        uint32_t popcount = 0;
        for (uint32_t i = 0; i != size; i++) {
            uint64_t tmp = mp[i];
            while(tmp) {
                popcount += tmp & 1;
                tmp >>= 1;
            }
        }
        return popcount == 1;
        #endif
    }

    bool popcnt_is_one(uint32_t from) const
    {
        from++;

        uint64_t tmp = mp[from/64];
        tmp >>= from%64;
        if (tmp) return false;

        for (uint32_t i = from/64+1; i != size; i++)
            if (mp[i]) return false;
        return true;
    }

    inline const uint64_t& is_true() const
    {
        return is_true_internal;
    }

    inline const bool isZero() const
    {
        for (uint32_t i = 0; i != size; i++) {
            if (mp[i]) return false;
        }
        return true;
    }

    inline void setZero()
    {
        memset(mp, 0, sizeof(uint64_t)*size);
    }

    inline void clearBit(const uint32_t i)
    {
        mp[i/64] &= ~((uint64_t)1 << (i%64));
    }

    inline void invert_is_true(const bool b = true)
    {
        is_true_internal ^= (uint64_t)b;
    }

    inline void setBit(const uint32_t i)
    {
        mp[i/64] |= ((uint64_t)1 << (i%64));
    }
	
	inline void setBit_two(const uint32_t i , const uint32_t j , bool xorEqualFalse)  // add by hankf4
    {
        mp[i/64] |= ((uint64_t)1 << (i%64));
		mp[j/64] |= ((uint64_t)1 << (j%64));
		is_true_internal = xorEqualFalse;
    }
	
	inline void setBit_three(const uint32_t i , const uint32_t j , const uint32_t k , bool xorEqualFalse)  // add by hankf4
    {
        mp[i/64] |= ((uint64_t)1 << (i%64));
		mp[j/64] |= ((uint64_t)1 << (j%64));
		mp[k/64] |= ((uint64_t)1 << (k%64));
		is_true_internal = xorEqualFalse;
    }


    void swapBoth(PackedRow b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        uint64_t * __restrict mp1 = mp-1;
        uint64_t * __restrict mp2 = b.mp-1; 

        //uint32_t i = 2*(size+1);
		uint32_t i = (size+1);
        while(i != 0) {
            std::swap(*mp1, *mp2);
            mp1++;
            mp2++;
            i--;
        }
    }
	// add by hankf4 , using one row copy to another row 
	void copyRow(PackedRow b){
        
		#ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        uint64_t * __restrict mp1 = mp-1;
        uint64_t * __restrict mp2 = b.mp-1;

        uint32_t i = (size+1);

        while(i != 0) {
			*mp1 =  *mp2;
            mp1++;
            mp2++;
            i--;
        }
	}
	// add by hankf4 , using find nonbasic and basic value
    uint32_t find_watchVar(vec<Lit>& tmp_clause, const vector<Var>& col_to_var,vec<bool> &GasVar_state , uint32_t& nb_var );
	//void find_watchVar2( vector < Var > &col_to_var ,uint32_t& b_var , uint32_t& nb_var ,uint32_t& nb_var2);
	// add by hankf4 , using find nonbasic, nonbasic2 and basic value
    uint32_t find_watchVar_2(vec<Lit>& tmp_clause, const vector<Var>& col_to_var,vec<bool> &GasVar_state , uint32_t& nb_var, uint32_t& nb_var2 );

	// add by hankf4 , using find nonbasic value after watch list is enter
	int propGause(vec<Lit>& tmp_clause,const vec<lbool>& assigns, const vector<Var>& col_to_var, vec<bool> &GasVar_state ,uint32_t& nb_var , uint32_t start);
	
	//  add by hankf4 , using add learnt clause which size = 3
    int propGause_add_learnt_two(vec<Lit>& tmp_clause,const vec<lbool>& assigns, const vector<Var>& col_to_var, vec<bool> &GasVar_state ,uint32_t& nb_var , uint32_t start,uint32_t& row_size);


    // add by hankf4 , using find nonbasic value after watch list is enter for 3 value watch
	int propGause2(vec<Lit>& tmp_clause,const vec<lbool>& assigns, const vector<Var>& col_to_var, vec<bool> &GasVar_state ,uint32_t& nb_var ,const uint32_t start , const uint32_t nb_var2 );

	// add by hankf4 , using find nonbasic value after watch list is enter for 3 value watch  in gaussian elimination
	int propGause_elimination(vec<Lit>& tmp_clause,const vec<lbool>& assigns, const vector<Var>& col_to_var, vec<bool> &GasVar_state ,const uint32_t start, const uint32_t p , uint32_t& nb_var ,uint32_t& nb_var2 , uint32_t& random_nb  );

	
	void debug_basic(const vector<Var>& col_to_var , vec<bool> &GasVar_state){
		uint32_t basic_num = 0;
		//printf("b:");
		uint32_t  tmp_var = 0;
		for(uint32_t i = 0; i < size*64; i++) {
			if (this->operator[](i)){
				tmp_var = col_to_var[i];
				if( GasVar_state[tmp_var] ){  //nobasic 
				//	printf("%d ",tmp_var);
					basic_num++;
				}
			}
		}
		assert(basic_num == 1 || basic_num == 0); 
	}
	
	inline const bool operator[](const uint32_t& i) const
    {
        #ifdef DEBUG_ROW
        assert(size*64 > i);
        #endif

        return (mp[i/64] >> (i%64)) & 1;
    }

    template<class T>
    void set(const T& v, const vector<Var>& var_to_col, const uint32_t matrix_size)
    {
		//(xorclause, var_to_col, origMat.num_cols)
        assert(size == (matrix_size/64) + ((bool)(matrix_size % 64)));
        //mp = new uint64_t[size];
        setZero();
        for (uint32_t i = 0; i != v.size(); i++) {
            const uint32_t toset_var = var_to_col[v[i].var()];
            assert(toset_var != std::numeric_limits<uint32_t>::max());

            setBit(toset_var);
        }

        is_true_internal = !v.xorEqualFalse();
    }

    const bool fill(vec<Lit>& tmp_clause, const vec<lbool>& assigns, const vector<Var>& col_to_var_original) const;

    inline unsigned long int scan(const unsigned long int var) const
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        #endif

        for(uint32_t i = var; i != size*64; i++) {
            if (this->operator[](i)) return i;
        }

        return std::numeric_limits<unsigned long int>::max();
    }

private:
    friend class PackedMatrix;
    friend std::ostream& operator << (std::ostream& os, const PackedRow& m);

    PackedRow(const uint32_t _size, uint64_t*  const _mp) :
        mp(_mp+1)
        , is_true_internal(*_mp)
        , size(_size)
    {}

    uint64_t* __restrict const mp;
    uint64_t& is_true_internal;
    const uint32_t size;
};

inline std::ostream& operator << (std::ostream& os, const PackedRow& m)
{
    for(uint32_t i = 0; i < m.size*64; i++) {
        os << m[i];
    }
    os << " -- xor: " << m.is_true();
    return os;
}

}

#endif //PACKEDROW_H
