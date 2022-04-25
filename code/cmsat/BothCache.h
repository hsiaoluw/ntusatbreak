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

#ifndef BOTHCACHE_H
#define BOTHCACHE_H

#include "cmsat/Solver.h"


#include <vector>
#include <set>
#include <iostream>
#include <algorithm>
#include <set>
#include "cmsat/CSet.h"
//#include "xorfinderabst.h"

namespace CMSat {
using std::vector;
using std::set;
using std::endl;
using std::cout;

class Simplifier;
class Solver;

class XorFinderAbst
{
    public:
        virtual bool findXors(double& totaltime ) = 0;
        virtual ~XorFinderAbst()
        {}
        virtual uint64_t memUsed() const = 0;
};


class Xor2
{
    public:
        Xor2(const vec<Lit>& cl, const bool _rhs) :
            rhs(_rhs)
        {
            for (uint32_t i = 0; i < cl.size(); i++) {
                vars.push_back(cl[i].var());
            }
            std::sort(vars.begin(), vars.end());
        }

        bool operator==(const Xor2& other) const
        {
            return (rhs == other.rhs && vars == other.vars);
        }

        vector<Var> vars;
        bool rhs;
};

inline std::ostream& operator<<(std::ostream& os, const Xor2& thisXor)
{
    for (uint32_t i = 0; i < thisXor.vars.size(); i++) {
        os << Lit(thisXor.vars[i], false);

        if (i+1 < thisXor.vars.size())
            os << " + ";
    }
    os << " =  " << std::boolalpha << thisXor.rhs << std::noboolalpha;

    return os;
}

class FoundXors
{
    public:
        FoundXors(
            const vec<Lit>& cl
            , CL_ABST_TYPE abst
            , vector<unsigned char>& seen
        ) :
            abst(abst)
            , size(cl.size())
        {
            #ifdef VERBOSE_DEBUG_XOR_FINDER
            cout << "Trying to create XOR from clause: " << cl << endl;
            #endif

            assert(cl.size() < sizeof(origCl)/sizeof(Lit));
            for(size_t i = 0; i < size; i++) {
                origCl[i] = cl[i];
                if (i > 0)
                    assert((cl[i-1].var() < cl[i].var() )|| (cl[i-1].var()==cl[i].var()));
            }

            calcClauseData(seen);
        }

        //GET-type functions
        CL_ABST_TYPE      getAbst() const;
        uint32_t          getSize() const;
        bool              getRHS() const;
        bool              foundAll() ;

        //Add
        template<class T> void add(const T& cl, vector<uint32_t>& varsMissing);
		
		bool getmoreXorinfo(Solver* solver);
	   

    public:
        void calcClauseData(vector<unsigned char>& seen)
        {
            //Calculate parameters of base clause.
            //Also set 'seen' for easy check in 'findXorMatch()'
            rhs = true;
            uint32_t whichOne = 0;
			alreadyfind.clear();
            for (uint32_t i = 0; i < size; i++) {
			   // printf("ori:%d%d ", origCl[i].var(), origCl[i].sign());
                rhs ^= origCl[i].sign();
                whichOne += ((uint32_t)origCl[i].sign()) << i;
                seen[origCl[i].var()] = 1;
				vector<Lit> tr; tr.clear(); tr.push_back(Lit(origCl[i].var(),true));
                vector<Lit> fs; fs.clear(); fs.push_back(Lit(origCl[i].var(),false));
                alreadyfind.push_back(tr);
                alreadyfind.push_back(fs);				
            }
            //printf("\n");
            foundComb.resize(1UL<<size, false);
            foundComb[whichOne] = true;
			
        }
        uint32_t NumberOfSetBits(uint32_t i) const;
        bool     bit(const uint32_t a, const uint32_t b) const;

        //bitfield to indicate which of the following is already set
        //-1 -2 -3
        //-1  2  3
        // 1 -2  3
        // 1  2 -3
        //order the above according to sign: if sign:
        //LSB ... MSB
        // 1 1 1
        // 1 0 0
        // 0 1 0
        // 0 0 1
        vector<bool> foundComb;
		vector<uint32_t>  odd_list;
		vector<uint32_t>  even_list;
		vector<uint32_t>  odd_list_four;
		vector<uint32_t>  even_list_four;
		vector<uint32_t> checklist_v;
		vector<vector<Lit> > alreadyfind;
		vector<vector<uint32_t> >  checklist_s;
        Lit origCl[5];
        const CL_ABST_TYPE abst;
        uint16_t size;
        bool rhs;
		
		
};

class XorFinder2: public XorFinderAbst
{
public:
    //XorFinder2(Simplifier* subsumer, Solver* solver);
	XorFinder2(Solver* _solver ,vec<Clause*>& _cls);
    virtual bool findXors(double &totaltime);

    struct Stats
    {
        Stats() :
            //Time
            findTime(0)
            , extractTime(0)
            , blockCutTime(0)

            //XOR
            , foundXors(0)
            , sumSizeXors(0)
            , numVarsInBlocks(0)
            , numBlocks(0)

            //Usefulness
            , newUnits(0)
            , newBins(0)
            , zeroDepthAssigns(0)
        {}

        void clear()
        {
            Stats tmp;
            *this = tmp;
        }

        double totalTime() const
        {
            return findTime + extractTime + blockCutTime;
        }

        Stats& operator+=(const Stats& other)
        {
            //Time
            findTime += other.findTime;
            extractTime += other.extractTime;
            blockCutTime += other.blockCutTime;

            //XOR
            foundXors += other.foundXors;
            sumSizeXors += other.sumSizeXors;
            numVarsInBlocks += other.numVarsInBlocks;
            numBlocks += other.numBlocks;

            //Usefulness
            newUnits += other.newUnits;
            newBins += other.newBins;
            zeroDepthAssigns += other.zeroDepthAssigns;

            return *this;
        }

        /*void printShort() const
        {
            cout
            << "c XOR finding "
            << " Num XORs: " << std::setw(6) << foundXors
            << " avg size: " << std::setw(4) << std::fixed << std::setprecision(1)
            << ((double)sumSizeXors/(double)foundXors)

            << " T: "
            << std::fixed << std::setprecision(2) << findTime
            << endl;

            cout
            << "c Cut XORs into " << numBlocks << " block(s)"
            << " sum vars: " << numVarsInBlocks
            << " T: " << std::fixed << std::setprecision(2) << blockCutTime
            << endl;

            cout
            << "c Extracted XOR info."
            << " Units: " << newUnits
            << " Bins: " << newBins
            << " 0-depth-assigns: " << zeroDepthAssigns
            << " T: " << std::fixed << std::setprecision(2) << extractTime
            << endl;
        }*/

        /*void print(const size_t numCalls) const
        {
            cout << "c --------- XOR STATS ----------" << endl;
            printStatsLine("c num XOR found on avg"
                , (double)foundXors/(double)numCalls
                , "avg size"
            );

            printStatsLine("c XOR avg size"
                , (double)sumSizeXors/(double)foundXors
            );

            printStatsLine("c XOR 0-depth assings"
                , zeroDepthAssigns
            );

            printStatsLine("c XOR unit found"
                , newUnits
            );

            printStatsLine("c XOR bin found"
                , newBins
            );
            cout << "c --------- XOR STATS END ----------" << endl;
        }*/

        //Time
        double findTime;
        double extractTime;
        double blockCutTime;

        //XOR stats
        uint64_t foundXors;
        uint64_t sumSizeXors;
        uint64_t numVarsInBlocks;
        uint64_t numBlocks;

        //Usefulness stats
        uint64_t newUnits;
        uint64_t newBins;

        size_t zeroDepthAssigns;
    };

    virtual ~XorFinder2()
    {}

    const Stats& getStats() const;
    size_t getNumCalls() const;
    virtual uint64_t memUsed() const;

private:

    int64_t maxTimeFindXors;

    //Find XORs
    void findXor(vec<Lit>& lits, CL_ABST_TYPE abst);

    ///Normal finding of matching clause for XOR
    void findXorMatch(
        const vec<Watched>& ws
        , const Lit lit
        , FoundXors& foundCls
    );
    
	/// found xor with cache
	void findXorMatch(
	const vector<Lit>& occ
    , const Lit lit
    , FoundXors& foundCls);

	
	
   
    //TODO stamping finXorMatch with stamp
    /*void findXorMatch(
        const vec<LitExtra>& lits
        , const Lit lit
        , FoundXors& foundCls
    ) const;*/


    //const uint32_t tryToXor(const Xor& thisXor, const uint32_t thisIndex);
    //bool mixXorAndGates();

    //Information extraction
    //bool extractInfo();
    //void cutIntoBlocks(const vec<size_t>& xorsToUse);
    //bool extractInfoFromBlock(const vec<Var>& block, const size_t blockNum);
    //vec<size_t> getXorsForBlock(const size_t blockNum);

    //Major calculated data and indexes to this data
    vector<Xor2> xors; ///<Recovered XORs
    vector<vector<uint32_t> > xorOcc;
    std::set<ClauseOffset> triedAlready; ///<These clauses have been tried to be made into an XOR. No point in tryin again
    vector<vector<Var> > blocks; ///<Blocks of vars that are in groups of XORs
    vector<size_t> varToBlock; ///<variable-> block index map

   // Simplifier* subsumer;
    Solver * solver;
    vec<Clause*>& cls;
    //Stats
    Stats runStats;
    Stats globalStats;
    size_t numCalls;

    //Temporary
    vec<Lit> tmpClause;
    vector<uint32_t> varsMissing;
    vector<ClauseOffset> offset_wait;
    //Temporaries for putting xors into matrix, and extracting info from matrix
    vector<size_t> outerToInterVarMap;
    vector<size_t> interToOUterVarMap;

    //Other temporaries
    vector<unsigned char> seen;
	bool needprint;
	//bool findxor;
    //vec<unsigned char>& seen2;
};


inline CL_ABST_TYPE FoundXors::getAbst() const
{
    return abst;
}

inline uint32_t FoundXors::getSize() const
{
    return size;
}

inline bool FoundXors::getRHS() const
{
    return rhs;
}

template<class T> void FoundXors::add(
    const T& cl
    , vector<uint32_t>& varsMissing
) {
    #ifdef VERBOSE_DEBUG_XOR_FINDER
    cout << "Adding to XOR: " << cl << endl;

    cout << "FoundComb before:" << endl;
    for(size_t i = 0; i < foundComb.size(); i++) {
        cout << "foundComb[" << i << "]: " << foundComb[i] << endl;
    }
    cout << "----" << endl;
    #endif

    assert(cl.size() <= size);
	if(cl.size()==2)
	{
	   assert(cl[0].toInt()<cl[1].toInt());   
	   for(uint32_t i=0;i<alreadyfind.size();i++)
	   {
	      vector<Lit>& now=alreadyfind[i];
		  if(now[0].toInt()==cl[0].toInt())
		  {  
		     bool found =false;
		     for(uint32_t j=1;j<now.size();j++)
			   {  if(now[j].toInt()==cl[1].toInt()) 
			   {found=true; 
			   return;}
			   }
		     if(!found)now.push_back(cl[1]);
			 
			 break;
		  }
	   }
	}

    //If clause covers more than one combination, this is used to calculate which ones
    varsMissing.clear();

    //Position of literal in the ORIGINAL clause.
    //This may be larger than the position in the current clause (as some literals could be missing)
    uint32_t origI = 0;

    //Position in current clause
    uint32_t i = 0;

    //Used to calculate this clause covers which combination(s)
    uint32_t whichOne = 0;

    bool thisRhs = true;

    for (typename T::const_iterator
        l = cl.begin(), end = cl.end()
        ; l != end
        ; l++, i++, origI++
    ) {
        thisRhs ^= l->sign();
        //printf("add:%d%d ",cl[i].var(),l->sign());
        //some variables might be missing in the middle
        while(cl[i].var() != origCl[origI].var()) {
            varsMissing.push_back(origI);
            origI++;
            assert(origI < size && "cl must be sorted");
        }
        whichOne += ((uint32_t)l->sign()) << origI;
    }
     //printf("\n");
    //if vars are missing from the end
    while(origI < size) {
        varsMissing.push_back(origI);
        origI++;
    }

    assert(cl.size() < size+1);

    //set to true every combination for the missing variables
    for (uint32_t i = 0; i < 1UL<<(varsMissing.size()); i++) {
        uint32_t thisWhichOne = whichOne;
        for (uint32_t i2 = 0; i2 < varsMissing.size(); i2++) {
            if (bit(i, i2)) thisWhichOne+= 1<<(varsMissing[i2]);
        }
        foundComb[thisWhichOne] = true;
    }

    #ifdef VERBOSE_DEBUG_XOR_FINDER
    cout << "whichOne was:" << whichOne << endl;
    cout << "FoundComb after:" << endl;
    for(size_t i = 0; i < foundComb.size(); i++) {
        cout << "foundComb[" << i << "]: " << foundComb[i] << endl;
    }
    cout << "----" << endl;
    #endif
}



 

inline uint32_t FoundXors::NumberOfSetBits(uint32_t i) const
{
    //Magic is coming! (copied from some book.... never trust code like this!)
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0xF0F0F0F) * 0x1010101) >> 24;
}

inline bool FoundXors::bit(const uint32_t a, const uint32_t b) const
{
    return (((a)>>(b))&1);
}



inline const XorFinder2::Stats& XorFinder2::getStats() const
{
    return globalStats;
}

inline size_t XorFinder2::getNumCalls() const
{
    return numCalls;
}







class BothCache
{
    public:
        BothCache(Solver& solver);
        bool tryBoth();

    private:
        Solver& solver;
};




}

#endif //BOTHCACHE_H
