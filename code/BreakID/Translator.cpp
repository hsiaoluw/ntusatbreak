/*
 * Translator.cpp
 *
 *  Created on: Jan 30, 2013
 *      Author: jodv
 */

#include "Translator.h"
#include "Symmetry.h"
#include "SymmetryGroup.h"

namespace sym {

Translator::Translator(unsigned int v, unsigned int c, string& in, string& out)
		: 	oldNumVars(v),
			oldNumClauses(c),
			numVars(v),
			numClauses(c),
			cnfClauses(in),
			outFileName(out) {
}

Translator::~Translator() {
}

unsigned int Translator::getNext() {
	numVars = next(numVars);
	return numVars;
}

/*
 * expects non-dimacs lits (== unsigned ints)
 */
void Translator::printClause(vector<int>& clause, ofstream& outFile) {
	for (auto lit : clause) {
		outFile << lit2dimacs(lit) << " ";
	}
	outFile << "0\n";
	++numClauses;
}

void Translator::addClause(int a, int b) {
	vector<int> clause { a, b };
	//printClause(clause);
	clauses.push_back(clause);
}

void Translator::addClause(int a, int b, int c) {
	vector<int> clause { a, b, c };
	//printClause(clause);
	clauses.push_back(clause);
}

/*
 * T <=(>) (T1 & T2)
 * is equivalent to
 * ~T | T1 (optional)
 * ~T | T2 (optional)
 *  T |~T1 |~T2
 */
void Translator::addConjunctiveDefinition(unsigned int t, int t1, int t2, bool shortened) {
	if (!shortened) {
		addClause(neg(t), t1);
		addClause(neg(t), t2);
	}
	addClause(t, neg(t1), neg(t2));
}

// TODO: make this an implication definition (both directions will be needed, maybe not so good?)
/*
 * T <=> (A<=>B) (with
 * is equivalent to
 * ~T | ~A |  B
 * ~T |  A | ~B
 *  T | ~A | ~B
 *  T |  A |  B
 */
void Translator::addEquivalenceDefinition(unsigned int a, unsigned int b, unsigned int t) {
	addClause(neg(t), neg(a), b);
	addClause(neg(t), a, neg(b));
	addClause(t, neg(a), neg(b));
	addClause(t, a, b);
}

void Translator::write() {
	if (verbosity > 0) {
		cout << "c Writing cnf file...\n";
	}
	ofstream outFile;
	outFile.open(outFileName);
	outFile << "c Tseitin variables added by symmetry breaking start at:\n";
	outFile << "c " << oldNumVars + 1 << "\n";
	outFile << "p cnf " << lit2dimacs(numVars) << " " << numClauses + clauses.size() << "\n";
	outFile << cnfClauses;
	if (cnfClauses.back() != '\n') { // printing clauses from cnf file, should always end with '\n';
		outFile << "\n";
	}
	for (auto sc : clauses) {
		printClause(sc, outFile);
	}
	outFile.close();
}

} /* namespace sym */
