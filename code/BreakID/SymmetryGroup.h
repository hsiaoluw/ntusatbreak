/*
 * SymmetryGroup.h
 *
 *  Created on: Jan 21, 2013
 *      Author: jodv
 */

#ifndef SYMMETRYGROUP_H_
#define SYMMETRYGROUP_H_

#include "Tools.h"
#include "Symmetry.h"
using namespace std;

namespace sym {

class Symmetry;
class Orbit;
class Translator;

struct classcomp {
	bool operator()(shared_ptr<Symmetry> first, shared_ptr<Symmetry> second) const {
		return first->compareTo(second) > 0;
	}
};

class SymmetryGroup {
private:
	shared_ptr<Translator> trans;
	unordered_set<shared_ptr<Symmetry> > generators;
	set<shared_ptr<Symmetry>, classcomp> breakingSyms;
	vector<shared_ptr<Symmetry> > columnSyms;

	vector<unsigned int> decompression;

	vector<unordered_map<unsigned int, unsigned int> > eqTseitins;
	unordered_map<int, unordered_map<int, unsigned int> > conjTseitins;

	vector<vector<vector<int>*>*> columnGroups;

	void addGenerator(shared_ptr<Symmetry>);
	void calculateOrdering(vector<int>& result);
	void addComposition(vector<shared_ptr<Symmetry> >& sym, unsigned int maxLength, set<shared_ptr<Symmetry>, classcomp>& compositions,
			vector<shared_ptr<Symmetry> >& newlyAdded, unordered_map<shared_ptr<Symmetry>, unordered_map<shared_ptr<Symmetry>, unsigned int> >& lengths);
	void calcLength(shared_ptr<Symmetry> first, shared_ptr<Symmetry> second, unsigned int& maxLength, set<shared_ptr<Symmetry>, classcomp>& compositions,
			unordered_map<shared_ptr<Symmetry>, unordered_map<shared_ptr<Symmetry>, unsigned int> >& lengths, vector<shared_ptr<Symmetry> >& newlyAdded);
	void extractSmallSymmetries(vector<shared_ptr<Symmetry> >& oldSyms, set<shared_ptr<Symmetry>, classcomp>& compositions, unsigned int index);
	string sym2string(shared_ptr<Symmetry> s, unsigned int verb);
	void generateBreakingConstraint(shared_ptr<Symmetry> sym, vector<int>& order, bool columnSym);
	void addSym(shared_ptr<Symmetry> inSym);
	void eraseSym(shared_ptr<Symmetry> inSym);
	bool isValidOrdering(vector<int>& ordering);
	void getImage(int lit, vector<int>& partialOrder, unordered_set<int>& result, unordered_set<int>& forbiddenLits, vector<shared_ptr<Symmetry> >& syms);

public:
	SymmetryGroup(vector<shared_ptr<map<unsigned int, int> > >&, shared_ptr<Translator> trans);
	virtual ~SymmetryGroup();
	string toString();
	unsigned int litUpperBound();
	unsigned int getSize();
	unsigned int generatorSetSize();
	bool extractOneRelatedSymSet(vector<shared_ptr<Symmetry> >& input, vector<vector<int>*>* columnGroup);
	void extractRelatedSymSets(set<shared_ptr<Symmetry>, classcomp>& inSyms, vector<vector<vector<int>*>*>& outSyms);
	void checkForRelatedSyms(unsigned int index);
	int decompress(int lit);
	unsigned int compress(unsigned int);
	void constructSymBreakingFormula();
	void constructShortestConstraints(vector<int>& order);
	void printStats();
	int getEquivalenceTseitin(int a, int b);
	unsigned int getConjTseitin(int a, int b);
	void eraseEmbeddedSyms();
};

} /* namespace sym */
#endif /* SYMMETRYGROUP_H_ */
