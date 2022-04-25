/*
 * Symmetry.h
 *
 *  Created on: Jan 21, 2013
 *      Author: jodv
 */

#ifndef SYMMETRY_H_
#define SYMMETRY_H_

#include "Tools.h"
using namespace std;

namespace sym {

class SymmetryGroup;

//TODO: make internal vector range over variables instead of literals
// e.g.: sym[0]=0 and sym[-x]=-sym[x].
//TODO: make this a finalized class
class Symmetry: public enable_shared_from_this<Symmetry> {
private:
	bool is_involution;
	void calculateLastsOfCycle(unordered_set<int>& lastsInCycle, vector<int>& order);
	map<unsigned int, int> usefulSteps; //second argument is the literal of the step

	bool isValidSplit(vector<shared_ptr<Symmetry> >& splits);

	// symmetry core info:
	vector<unsigned int> support;
	vector<int> sym;
	unsigned int sym_min;
	unsigned int sym_max;

	bool canSet(unsigned int index, int value);

public:
	Symmetry();
	Symmetry(unordered_map<unsigned int, int>& values);
	Symmetry(shared_ptr<Symmetry>, shared_ptr<Symmetry>);
	virtual ~Symmetry();

	string toString();
	bool equals(shared_ptr<Symmetry>);
	int symmetrical(int);
	bool isIdentity();
	bool isInvolution();
	unsigned int supportSize();
	unsigned int get(unsigned int index);
	int compareTo(shared_ptr<Symmetry>);
	void calculateUsableLits(vector<int>& result, vector<int>& order);
	unsigned int minLit();
	unsigned int maxLit();
	shared_ptr<Symmetry> after(shared_ptr<Symmetry> other);
	void findBetterConstraints(unordered_map<int, unordered_map<int, pair<shared_ptr<Symmetry>, unsigned int> > >& bestConstraints, vector<int>& order);
	void decreaseUsefulness(unsigned int step);
	void increaseUsefulness(unsigned int step, int lit);
	unsigned int getMaxStep();
	unsigned int getNumberOfSteps();
	void split(vector<shared_ptr<Symmetry> >& splits);
	bool isCompatibleWith(shared_ptr<Symmetry> other);
	bool isDisjunctWith(shared_ptr<Symmetry> other);
	bool sharesOneColumn(shared_ptr<Symmetry> other1, shared_ptr<Symmetry> other2);
	void getCycles(vector<shared_ptr<vector<int> > >& cycles);
	bool overlapsWith(vector<int>& lits);
	bool supportIsSubset(unordered_set<int>& lits);
	void resetSteps();
	void getColumns(shared_ptr<Symmetry> other, vector<vector<int>*>* columns);
	void extendColumns(vector<vector<int>*>* columns);
};

} /* namespace sym */
#endif /* SYMMETRY_H_ */
