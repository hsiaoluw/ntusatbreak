/*
 * Translator.h
 *
 *  Created on: Jan 30, 2013
 *      Author: jodv
 */

#ifndef TRANSLATOR_H_
#define TRANSLATOR_H_

#include "Tools.h"
#include <fstream>

namespace sym {

class Symmetry;

class Translator {
private:
	const unsigned int oldNumVars;
	const unsigned int oldNumClauses;
	unsigned int numVars;
	unsigned int numClauses;

	string cnfClauses;
	string outFileName;

	vector<vector<int> > clauses;

public:
	Translator(unsigned int, unsigned int, string&, string&);
	virtual ~Translator();
	void printClause(vector<int>&, ofstream& outFile);
	void addClause(int, int);
	void addClause(int, int, int);
	void addConjunctiveDefinition(unsigned int t, int t1, int t2, bool shortened);
	void addEquivalenceDefinition(unsigned int a, unsigned int b, unsigned int t);
	unsigned int getNext();
	void write();
}
;

} /* namespace sym */
#endif /* TRANSLATOR_H_ */
