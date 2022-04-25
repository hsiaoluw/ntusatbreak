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

#include "cmsat/MatrixFinder.h"
#include "cmsat/Solver.h"
//#include "cmsat/Gaussian.h"
#include "cmsat/GaussianConfig.h"
#include "cmsat/ClauseCleaner.h"
#include "cmsat/time_mem.h"
#include "cmsat/EnhanceGaussian.h"
#include <set>
#include <map>
#include <iomanip>
#include <math.h>

//#define VERBOSE_DEBUG
//#define PART_FINDING

using namespace CMSat;

using std::set;
using std::map;

MatrixFinder::MatrixFinder(Solver& _solver) :
    solver(_solver)
{
}


inline const Var MatrixFinder::fingerprint(const XorClause& c) const
{
    Var fingerprint = 0;

    for (const Lit* a = &c[0], *end = a + c.size(); a != end; a++)
        fingerprint |= a->var();

    return fingerprint;
}

inline const bool MatrixFinder::firstPartOfSecond(const XorClause& c1, const XorClause& c2) const
{
    uint32_t i1, i2;
    for (i1 = 0, i2 = 0; i1 < c1.size() && i2 < c2.size();) {
        if (c1[i1].var() != c2[i2].var())
            i2++;
        else {
            i1++;
            i2++;
        }
    }

    return (i1 == c1.size());
}

const bool MatrixFinder::findMatrixes()
{
    assert(solver.decisionLevel() == 0);
    assert(solver.ok);
	
    table.clear();   //var -> matrix
    table.resize(solver.nVars(), var_Undef);
    reverseTable.clear(); //matrix -> vars /
    matrix_no = 0;
	double myTime = cpuTime();


	// MIN_GAUSS_XOR_CLAUSES = 5
	// MAX_GAUSS_XOR_CLAUSES = 30000
    if (solver.xorclauses.size() < MIN_GAUSS_XOR_CLAUSES ||
        solver.gaussconfig.decision_until <= 0 ||
        solver.xorclauses.size() > (MAX_GAUSS_XOR_CLAUSES+solver.additional_morexor)
        ) {
		//printf("Warring!!!! xor clauss size can not build matrix in findMatrixes \n");	
        return true;
    }

    solver.clauseCleaner->cleanClauses(solver.xorclauses, ClauseCleaner::xorclauses);
    if (!solver.ok){ 
		//printf("Warring!!!! solver ok is false in findMatrixes \n");
		return false;
	}
	
	// this if seems can not enter
    /*if (solver.gaussconfig.noMatrixFind) {
        //if (solver.conf.verbosity >=1)
		printf("Warring!!!!!");
            std::cout << "c Matrix finding disabled through switch. Putting all xors into matrix." << std::endl;
		assert(false); // debug by hankf4
	   vector<XorClause*> xorclauses;
        xorclauses.reserve(solver.xorclauses.size());
        for (uint32_t i = 0; i < solver.xorclauses.size(); i++)
            xorclauses.push_back(solver.xorclauses[i]);
        solver.gauss_matrixes.push_back(new Gaussian(solver, solver.gaussconfig, 0, xorclauses));
        return true;
    }*/
	
	


	// figure 4
    for (XorClause** c = solver.xorclauses.getData(), **end = c + solver.xorclauses.size(); c != end; c++) {
        set<uint32_t> tomerge;
        vector<Var> newSet;
        for (Lit *l = &(**c)[0], *end2 = l + (**c).size(); l != end2; l++) {
            if (table[l->var()] != var_Undef)
                tomerge.insert(table[l->var()]);
            else
                newSet.push_back(l->var());
        }
        if (tomerge.size() == 1) {
            const uint32_t into = *tomerge.begin();
            map<uint32_t, vector<Var> >::iterator intoReverse = reverseTable.find(into);
            for (uint32_t i = 0; i < newSet.size(); i++) {
                intoReverse->second.push_back(newSet[i]);
                table[newSet[i]] = into;
            }
            continue;
        }

        for (set<uint32_t>::iterator it = tomerge.begin(); it != tomerge.end(); it++) {
            newSet.insert(newSet.end(), reverseTable[*it].begin(), reverseTable[*it].end());
            reverseTable.erase(*it);
        }
        for (uint32_t i = 0; i < newSet.size(); i++)
            table[newSet[i]] = matrix_no;
        reverseTable[matrix_no] = newSet;
        matrix_no++;
    }

    #ifdef VERBOSE_DEBUG
    for (map<uint32_t, vector<Var> >::iterator it = reverseTable.begin(), end = reverseTable.end(); it != end; it++) {
        std::cout << "-- set begin --" << std::endl;
        for (vector<Var>::iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
            std::cout << *it2 << ", ";
        }
        std::cout << "-------" << std::endl;
    }
    #endif
	

    uint32_t numMatrixes = setMatrixes();

	if (solver.conf.verbosity >=1)
        std::cout << "c Finding matrixes :    " << cpuTime() - myTime
        << " s (found  " << numMatrixes << ")"
        << std::endl;
		
	// delete by hankf4	
/*     for (vector<Gaussian*>::iterator gauss = solver.gauss_matrixes.begin(), end = solver.gauss_matrixes.end(); gauss != end; gauss++) {
        if (!(*gauss)->full_init()) return false;
    } */
	// add by hankf4
	//printf("findMatrix\n");
	solver.EnhancGauss_matrixes_size = numMatrixes;
	for (vector<EnhanceGaussian*>::iterator gauss = solver.EnhancGauss_matrixes.begin(), end = solver.EnhancGauss_matrixes.end(); gauss != end; gauss++) {
		if (!(*gauss)->full_init()) 
            return false;	
	}
	

    return true;
}

const uint32_t MatrixFinder::setMatrixes()
{
	
    vector<pair<uint32_t, uint32_t> > numXorInMatrix;
	
    for (uint32_t i = 0; i < matrix_no; i++)
        numXorInMatrix.push_back(std::make_pair(i, 0));
		

    vector<uint32_t> sumXorSizeInMatrix(matrix_no, 0);
    vector<vector<uint32_t> > xorSizesInMatrix(matrix_no);
    vector<vector<XorClause*> > xorsInMatrix(matrix_no);

    #ifdef PART_FINDING
    vector<vector<Var> > xorFingerprintInMatrix(matrix_no);
    #endif
	
	
	//  vector<Var> table; //var -> matrix
	//  map<uint32_t, vector<Var> > reverseTable; //matrix -> vars

    for (XorClause** c = solver.xorclauses.getData(), **end = c + solver.xorclauses.size(); c != end; c++) {
        XorClause& x = **c;
        const uint32_t matrix = table[x[0].var()];  // check this xor clause in which matrix
		
        assert(matrix < matrix_no);

        //for stats
        numXorInMatrix[matrix].second++;		     // the number of xorclause in matrix
        sumXorSizeInMatrix[matrix] += x.size();      // the number of xorclause size in matrix
        xorSizesInMatrix[matrix].push_back(x.size());  // xor clause size in matrix
        xorsInMatrix[matrix].push_back(&x);            // xor clause in  matrix

        #ifdef PART_FINDING
        xorFingerprintInMatrix[matrix].push_back(fingerprint(x));
        #endif //PART_FINDING
    }
	
	// this sort want to let the bigger number of xorclause matrix in first, because crypicalminisat want 3 matrix
    std::sort(numXorInMatrix.begin(), numXorInMatrix.end(), mysorter());

    #ifdef PART_FINDING
    for (uint32_t i = 0; i < matrix_no; i++)
        findParts(xorFingerprintInMatrix[i], xorsInMatrix[i]);
    #endif //PART_FINDING

    uint32_t realMatrixNum = 0;
	
	
	
    for (int a = matrix_no-1; a != -1; a--) {
        uint32_t i = numXorInMatrix[a].first;
		
		
        if (numXorInMatrix[a].second < 3)   // if only 3 xor clause, omit 
            continue;

		/************ not  check ****************/	
        const uint32_t totalSize = reverseTable[i].size()*numXorInMatrix[a].second;
        const double density = (double)sumXorSizeInMatrix[i]/(double)totalSize*100.0;
        double avg = (double)sumXorSizeInMatrix[i]/(double)numXorInMatrix[a].second;
        double variance = 0.0;       
	   for (uint32_t i2 = 0; i2 < xorSizesInMatrix[i].size(); i2++)
            variance += pow((double)xorSizesInMatrix[i][i2]-avg, 2);
        variance /= (double)xorSizesInMatrix.size();
        const double stdDeviation = sqrt(variance);
		/*****************************************/

		//printf("%d %d %d\n",solver.gaussconfig.minMatrixRows,solver.gaussconfig.maxMatrixRows, solver.gaussconfig.maxNumMatrixes);
        // solver.gaussconfig.minMatrixRows = 20
		// solver.gaussconfig.maxMatrixRows = 1000
		//  solver.gaussconfig.maxNumMatrixes = 3
		
		//solver.gaussconfig.minMatrixRows = 1;// for testing 
		
		if (numXorInMatrix[a].second >= solver.gaussconfig.minMatrixRows
            && numXorInMatrix[a].second <= solver.gaussconfig.maxMatrixRows
            && realMatrixNum <= solver.gaussconfig.maxNumMatrixes)
        {
            if (solver.conf.verbosity >=1)
                std::cout << "c Matrix no " << std::setw(2) << realMatrixNum;
				
			// delete by hankf4	
            //solver.gauss_matrixes.push_back(new Gaussian(solver, solver.gaussconfig, realMatrixNum, xorsInMatrix[i]));
            
			// add by hankf4 -1
			solver.EnhancGauss_matrixes.push_back(new EnhanceGaussian(solver, solver.gaussconfig, realMatrixNum, xorsInMatrix[i]));
           
			
			realMatrixNum++;

        } else {
            if (solver.conf.verbosity >=1  /*&& numXorInMatrix[a].second >= 20*/)
                std::cout << "c Unused Matrix ";
        }
        if (solver.conf.verbosity >=1 /*&& numXorInMatrix[a].second >= 20*/) {
            std::cout << std::setw(7) << numXorInMatrix[a].second << " x" << std::setw(5) << reverseTable[i].size();
            std::cout << "  density:" << std::setw(5) << std::fixed << std::setprecision(1) << density << "%";
            std::cout << "  xorlen avg:" << std::setw(5) << std::fixed << std::setprecision(2)  << avg;
            std::cout << " stdev:" << std::setw(6) << std::fixed << std::setprecision(2) << stdDeviation << std::endl;
        }
    }
	
	
	//printf("DD:Construct realMatrixNum:%d\n",realMatrixNum);

    return realMatrixNum;
}

void MatrixFinder::findParts(vector<Var>& xorFingerprintInMatrix, vector<XorClause*>& xorsInMatrix)
{
    uint32_t ai = 0;
    for (XorClause **a = &xorsInMatrix[0], **end = a + xorsInMatrix.size(); a != end; a++, ai++) {
        const Var fingerprint = xorFingerprintInMatrix[ai];
        uint32_t ai2 = 0;
        for (XorClause **a2 = &xorsInMatrix[0]; a2 != end; a2++, ai2++) {
            if (ai == ai2) continue;
            const Var fingerprint2 = xorFingerprintInMatrix[ai2];
            if (((fingerprint & fingerprint2) == fingerprint) && firstPartOfSecond(**a, **a2)) {
                std::cout << "First part of second:" << std::endl;
                (*a)->plainPrint();
                (*a2)->plainPrint();
                std::cout << "END" << std::endl;
            }
        }
    }
}
