/*
 * Symmetry.cpp
 *
 *  Created on: Jan 21, 2013
 *      Author: jodv
 */

#include "Symmetry.h"
#include "SymmetryGroup.h"

using namespace std;

namespace sym {

// this constructor constructs the identity
Symmetry::Symmetry() {
	sym_max = 0;
	sym_min = UINT_MAX;
	is_involution = false;
}

// this constructor constructs the symmetry defined by the given mapping
Symmetry::Symmetry(unordered_map<unsigned int, int>& values) {
	sym_max = 0;
	sym_min = UINT_MAX;
	if (values.size() == 0) {
		is_involution = false;
		return;
	}
	is_involution = true;

	for (auto i : values) {
		assert((int)i.first!=i.second);
		if (i.first > sym_max) {
			sym_max = i.first;
		}
		if (i.first < sym_min) {
			sym_min = i.first;
		}
		support.push_back(i.first); // NOTE: order of support is not fixed...
	}
	if (sym_max != 0 && sym_min != UINT_MAX) {
		sym.resize(sym_max - sym_min + 1);
		for (unsigned int i = 0; i < sym.size(); ++i) {
			assert(canSet(i,i+sym_min));
			sym[i] = sym_min + i;
		}
		for (auto i : values) {
			assert(canSet(i.first-sym_min,i.second));
			sym[i.first - sym_min] = i.second;
		}
	}

	// TODO: immediately calculate cycles...
	is_involution = true;
	for (unsigned int lit : support) {
		if ((int) lit != symmetrical(symmetrical(lit))) {
			is_involution = false;
			break;
		}
	}
}

// this constructor constructs the composition of the given symmetries
Symmetry::Symmetry(shared_ptr<Symmetry> after, shared_ptr<Symmetry> before) {

	//TODO: assert after o before is not an identity!
	assert(!after->isIdentity() && !before->isIdentity());

	unsigned int tmpMax = before->maxLit();
	if (tmpMax < after->maxLit()) {
		tmpMax = after->maxLit();
	}
	unsigned int tmpMin = before->minLit();
	if (tmpMin > after->minLit()) {
		tmpMin = after->minLit();
	}

	sym_max = 0;
	sym_min = UINT_MAX;
	for (unsigned int i = tmpMin; i <= tmpMax; ++i) {
		int symmetric = after->symmetrical(before->symmetrical(i));
		if ((int) i != symmetric) {
			if (sym_min == UINT_MAX) {
				sym_min = i;
				sym_max = i;
			} else {
				for (++sym_max; sym_max < i; ++sym_max) {
					sym.push_back(sym_max);
				}
				assert(sym_max==i);
			}
			sym.push_back(symmetric);
			support.push_back(i);
		}
	}

	// TODO: calculate cycles in constructor
	if (isIdentity()) {
		is_involution = false;
	} else {
		is_involution = true;
		for (unsigned int lit : support) {
			if ((int) lit != symmetrical(symmetrical(lit))) {
				is_involution = false;
				break;
			}
		}
	}
}

Symmetry::~Symmetry() {
}

int Symmetry::symmetrical(int in) {
	unsigned int pos_in = pos(in);
	if (pos_in < sym_min || pos_in > sym_max) {
		return in;
	} else {
		return commute(in, sym[pos_in - sym_min]);
	}
}

bool Symmetry::equals(shared_ptr<Symmetry> other) {
	return compareTo(other) == 0;
}

shared_ptr<Symmetry> Symmetry::after(shared_ptr<Symmetry> other) {
	if (other->isIdentity()) {
		return shared_from_this();
	} else if (isIdentity()) {
		return other;
	} else if (isInvolution() && shared_from_this() == other) { //composing an involution with itself yields the identity
		return make_shared<Symmetry>();
	} else {
		return make_shared<Symmetry>(shared_from_this(), other);
	}
}

bool Symmetry::isIdentity() {
	return sym.size() == 0;
}

bool Symmetry::isInvolution() {
	return is_involution;
}

unsigned int Symmetry::supportSize() {
	return support.size();
}

unsigned int Symmetry::get(unsigned int index) {
	return support.at(index);
}

int Symmetry::compareTo(shared_ptr<Symmetry> other) {
	if (shared_from_this() == other) {
		return 0;
	}
	if (supportSize() < other->supportSize()) {
		return 1;
	} else if (supportSize() > other->supportSize()) {
		return -1;
	}
	if (isInvolution() && !other->isInvolution()) {
		return 1;
	} else if (!isInvolution() && other->isInvolution()) {
		return -1;
	}
	if (minLit() < other->minLit()) {
		return 1;
	} else if (minLit() > other->minLit()) {
		return -1;
	}
	if (maxLit() < other->maxLit()) {
		return 1;
	} else if (maxLit() > other->maxLit()) {
		return -1;
	}
	// This check on min and max assures that x.compareTo(y)==-y.compareTo(x)
	assert(minLit()== other->minLit() && maxLit()==other->maxLit());
	for (unsigned int lit = minLit(); lit <= maxLit(); ++lit) {
		// NOTE: be careful when using support in this comparison:
		// 1. you want the comparison to be commutative
		// 2. there is currently no ordering for support: the same symmetries can have a differently ordered support
		if (symmetrical(lit) != other->symmetrical(lit)) {
			if (symmetrical(lit) < other->symmetrical(lit)) {
				return 1;
			} else {
				return -1;
			}
		}

	}
	return 0;
}

unsigned int Symmetry::minLit() {
	return sym_min;
}

unsigned int Symmetry::maxLit() {
	return sym_max;
}

// given an order, calculate which literals occur at the end of a cycle.
// NOTE: because of inverting symmetries, we cannot make use of the fact that symmetries commute with negation
void Symmetry::calculateLastsOfCycle(unordered_set<int>& lastsInCycle, vector<int>& order) {
	lastsInCycle.clear();
	unordered_set<unsigned int> checkedLits;
	for (unsigned int i = order.size(); i > 0; --i) {
		int lit = order.at(i - 1);
		int symmetric = symmetrical(lit);
		if (lit != symmetric && checkedLits.count(lit) == 0) {
			lastsInCycle.insert(lit);
			checkedLits.insert(lit);
			while (lit != symmetric) {
				checkedLits.insert(symmetric);
				symmetric = symmetrical(symmetric);
			}
		}
	}
}

// given an order on the literals, calculate which literals are useful to construct symmetry breaking clauses
// return: result does not contain both a literal and its negation
void Symmetry::calculateUsableLits(vector<int>& result, vector<int>& order) {
	result.clear();
	unordered_set<int> forbidden;
	calculateLastsOfCycle(forbidden, order);
	if (verbosity > 2) {
		cout << "lastsInCycle: ";
		for (auto lit : forbidden) {
			cout << lit << "|";
		}
		cout << "\n";
	}
	for (auto lit : order) {
		if (lit != symmetrical(lit) && forbidden.count(lit) == 0) {
			result.push_back(lit);
			forbidden.insert(neg(lit));
		}
		// TODO: argue why this limit of 100 is useful / needed
		if (result.size() >= 100 || neg(lit) == symmetrical(lit)) { //TODO: this check should be more profound, based on whether the literal's negation is present in the same cycle
			break;
		}
	}
}

//TODO: fix this long header :S
void Symmetry::findBetterConstraints(unordered_map<int, unordered_map<int, pair<shared_ptr<Symmetry>, unsigned int> > >& bestConstraints, vector<int>& order) {
	usefulSteps.clear();

	vector<int> usableLits;
	calculateUsableLits(usableLits, order);

	for (unsigned int i = 0; i < usableLits.size(); ++i) {
		int lit = usableLits.at(i);
		int symmetric = symmetrical(lit);
		assert(lit!=symmetric);
		shared_ptr<Symmetry> other = bestConstraints[lit][symmetric].first;
		unsigned int otherSteps = bestConstraints[lit][symmetric].second;
		if (!other || otherSteps > i) {
			increaseUsefulness(i, lit);
			if (other) {
				other->decreaseUsefulness(otherSteps);
			}
			bestConstraints[lit][symmetric].first = shared_from_this();
			bestConstraints[lit][symmetric].second = i;
		}
	}
}

void Symmetry::increaseUsefulness(unsigned int step, int lit) {
	assert(usefulSteps.count(step)==0);
	usefulSteps[step] = lit;
}

void Symmetry::decreaseUsefulness(unsigned int step) {
	assert(usefulSteps.count(step)!=0);
	usefulSteps.erase(step);
}

unsigned int Symmetry::getMaxStep() {
	assert(getNumberOfSteps()>0);
	return usefulSteps.crbegin()->first;
}

unsigned int Symmetry::getNumberOfSteps() {
	return usefulSteps.size();
}

inline
void assignFactorset(vector<shared_ptr<vector<int> > >& jointCycles, unordered_set<unsigned int>& jointFactors,
		vector<pair<shared_ptr<vector<unsigned int> >, shared_ptr<vector<int> > > >& factorsets, unsigned int index) {
	assert(index<factorsets.size());
	jointCycles.push_back(factorsets.at(index).second);
	for (auto factor : *(factorsets.at(index).first)) {
		jointFactors.insert(factor);
	}
	factorsets[index] = factorsets.back();
	factorsets.pop_back();
}

bool Symmetry::isValidSplit(vector<shared_ptr<Symmetry> >& splits) {
	assert(splits.size()>0);
	shared_ptr<Symmetry> start = splits.front();
	for (unsigned int i = 1; i < splits.size(); ++i) {
		start = splits.at(i)->after(start);
	}
	assert(compareTo(start) == 0);
	for (unsigned int i = 0; i < splits.size(); ++i) {
		for (unsigned int j = i + 1; j < splits.size(); ++j) {
			assert(splits.at(i)->isDisjunctWith(splits.at(j)));
		}
	}
	return true;
}

// return: the maximal split of this symmetry
void Symmetry::split(vector<shared_ptr<Symmetry> >& splits) {
	assert(splits.size()==0);
	if (isInvolution() || isIdentity()) {
		splits.push_back(shared_from_this());
		return;
	}

	// calculate cycles of this symmetry
	vector<shared_ptr<vector<int> > > cycles;
	getCycles(cycles);

	// calculate factorization of lengths of cycles
	vector<pair<shared_ptr<vector<unsigned int> >, shared_ptr<vector<int> > > > factorsets; // contains both the cycle and the factorset
	for (auto cycle : cycles) {
		shared_ptr<vector<unsigned int> > fset = make_shared<vector<unsigned int> >();
		factor(cycle->size(), *fset);
		assert(fset->size()>0);
		factorsets.push_back( { fset, cycle });
	}

	// Now look for all jointcycles
	// joint == their respective lengths share a prime factor
	while (factorsets.size() > 0) {
		// take as starting set for (dis)joint set algorithm the largest set
		unsigned int maxLength = 0;
		unsigned int maxIndex = 0;
		for (unsigned int i = 0; i < factorsets.size(); ++i) {
			if (maxLength < factorsets.at(i).first->size()) {
				maxLength = factorsets.at(i).first->size();
				maxIndex = i;
			}
		}

		vector<shared_ptr<vector<int> > > jointCycles;
		unordered_set<unsigned int> jointFactors;
		assignFactorset(jointCycles, jointFactors, factorsets, maxIndex);

		// Now check for each other factorset whether it has a common element.
		// If so, join. If not, leave it be.
		// If the size of the vector of sets doesn't change after a run,
		// disjoint sets have been found.
		unsigned int factorSetsSize = UINT_MAX;
		while (factorSetsSize > factorsets.size()) {
			factorSetsSize = factorsets.size();
			for (unsigned int i = factorsets.size(); i > 0; --i) {
				auto current = factorsets.at(i - 1);
				for (auto factor : *(current.first)) {
					if (jointFactors.count(factor) > 0) {
						assignFactorset(jointCycles, jointFactors, factorsets, i - 1);
						break;
					}
				}
			}
		}

		if (factorsets.size() == 0 && splits.size() == 0) {
			// no split has been found
			splits.push_back(shared_from_this());
		} else {
			// create a symmetry based on the set of jointCycles
			unordered_map<unsigned int, int> values;
			for (auto cycle : jointCycles) {
				for (unsigned int i = 0; i < cycle->size(); ++i) {
					unsigned int from = pos(cycle->at(i));
					int to = commute(cycle->at(i), cycle->at((i + 1) % cycle->size()));
					values.insert( { from, to });
				}
			}
			splits.push_back(make_shared<Symmetry>(values));
		}
	}
	assert(isValidSplit(splits));
}

//TODO: use this method in other methods of Symmetry.cpp
void Symmetry::getCycles(vector<shared_ptr<vector<int> > >& cycles) {
	assert(cycles.size()==0);
	if (isIdentity()) {
		return;
	}
	unordered_set<unsigned int> checkedLits;
	for (unsigned int lit : support) {
		int symLit = symmetrical(lit);
		if (checkedLits.count(lit) == 0) {
			checkedLits.insert(lit);
			shared_ptr<vector<int> > cycle = make_shared<vector<int> >();
			cycle->push_back(lit);
			while ((int) lit != symLit) { // the pos is to avoid duplicate inverted cycles...
				checkedLits.insert(pos(symLit));
				cycle->push_back(symLit);
				symLit = symmetrical(symLit);
			}
			cycles.push_back(cycle);
		}
	}
	assert(cycles.size()>0);
}

bool Symmetry::sharesOneColumn(shared_ptr<Symmetry> other1, shared_ptr<Symmetry> other2) {
	assert(isCompatibleWith(other1));
	assert(isCompatibleWith(other2));
	for (unsigned int lit : support) {
		// from the preconditions, we know that:
		assert((other1->symmetrical(lit)==(int)lit) != (other1->symmetrical(symmetrical(lit)) == symmetrical(lit)));
		assert((other2->symmetrical(lit)==(int)lit) != (other2->symmetrical(symmetrical(lit)) == symmetrical(lit)));
		if ((other1->symmetrical(lit) == (int) lit) != (other2->symmetrical(lit) == (int) lit)) {
			return false;
		} else {
			// so if the if-condition does not hold, then we know that the following holds:
			assert( (other1->symmetrical(lit)==(int)lit) == (other2->symmetrical(lit)==(int)lit));
			assert( (other1->symmetrical(symmetrical(lit))==(int)symmetrical(lit)) == (other2->symmetrical(symmetrical(lit))==(int)symmetrical(lit)));
		}
	}
	return true;
}

bool Symmetry::isCompatibleWith(shared_ptr<Symmetry> other) {
	assert(isInvolution());
	assert(other->isInvolution());
	assert(supportSize()==other->supportSize());
	for (auto lit : support) {
		int sym = symmetrical(lit);
		// we know lit!=sym
		int lit2 = other->symmetrical(lit);
		int sym2 = other->symmetrical(sym);
		if (lit2 != (int) lit) {
			// then sym == sym2 and symmetrical(lit2)==lit2 (and as a result, symmetrical(sym2)!=sym2)
			if (sym != sym2 || symmetrical(lit2) != lit2) {
				return false;
			}
		} else { // lit2==lit
				 // then sym != sym2 and symmetrical(sym2)==sym2 (and as a result, symmetrical(lit2)!=lit2)
			if (sym == sym2 || symmetrical(sym2) != sym2) {
				return false;
			}
		}
	}
	return true;
}

// if this is compatible with other, give the three columns, else, give zero columns
// columns will contain only half of the literals (rest is calculatable by commuting with negation)
void Symmetry::getColumns(shared_ptr<Symmetry> other, vector<vector<int>*>* columns) {
	assert(isInvolution());
	assert(other->isInvolution());
	assert(supportSize()==other->supportSize());
	assert(columns->size()==0);
	vector<int> firstcolumn;
	for (auto lit : support) {
		int sym = symmetrical(lit);
		// we know lit!=sym
		int lit2 = other->symmetrical(lit);
		int sym2 = other->symmetrical(sym);
		if (lit2 != (int) lit) {
			firstcolumn.push_back(lit);
			// then sym == sym2 and symmetrical(lit2)==lit2 (and as a result, symmetrical(sym2)!=sym2)
			if (sym != sym2 || symmetrical(lit2) != lit2) {
				columns->clear();
				return;
			}
		} else { // lit2==lit
				 // then sym != sym2 and symmetrical(sym2)==sym2 (and as a result, symmetrical(lit2)!=lit2)
			if (sym == sym2 || symmetrical(sym2) != sym2) {
				columns->clear();
				return;
			}
		}
	}
	// TODO: refactor
	for (unsigned int i = 0; i < 3; ++i) {
		columns->push_back(new vector<int>());
	}
	for (auto lit : firstcolumn) {
		columns->at(0)->push_back(lit);
		columns->at(1)->push_back(symmetrical(lit));
		columns->at(2)->push_back(other->symmetrical(lit));
	}
	assert(columns->at(0)->size()==support.size()/2);
}

void Symmetry::extendColumns(vector<vector<int>*>* columns) {
	assert(isInvolution());
	assert(columns->size()>=3);
	assert(columns->at(0)->size()*2==support.size());
	unsigned int numberOfSharedColumns = 0;
	int lastSharedColumn = -1;
	for (unsigned int i = 0; i < columns->size(); ++i) {
		bool sharesColumn = symmetrical(columns->at(i)->at(0)) != columns->at(i)->at(0);
		if (sharesColumn) {
			++numberOfSharedColumns;
			lastSharedColumn = i;
		}
		for (unsigned int j = 0; j < columns->at(i)->size(); ++j) {
			if (sharesColumn != (symmetrical(columns->at(i)->at(j)) != columns->at(i)->at(j))) {
				return;
			}
		}
	}

	if (numberOfSharedColumns == 1) {
		unordered_set<int> symLits;
		vector<int>* tmp = new vector<int>();
		for (auto lit : *(columns->at(lastSharedColumn))) {
			tmp->push_back(symmetrical(lit));
			if (symLits.count(lit) != 0) {
				return; // exceptional case where a symmetry actually does not share a column! e.g. column = [1,2,3,4] and symmetry = (1 2)(3 4)
			}
			symLits.insert(symmetrical(lit));
		}
		columns->push_back(tmp);
	}
}

bool Symmetry::isDisjunctWith(shared_ptr<Symmetry> other) {
	for (unsigned int lit : support) {
		if ((int) lit != other->symmetrical(lit)) {
			return false;
		}
	}
	return true;
}

bool Symmetry::overlapsWith(vector<int>& lits) {
	for (auto lit : lits) {
		if (symmetrical(lit) != lit) {
			return true;
		}
	}
	return false;
}

bool Symmetry::supportIsSubset(unordered_set<int>& lits) {
	for (auto lit : support) {
		if (lits.count(lit) == 0) {
			return false;
		}
	}
	return true;
}

bool Symmetry::canSet(unsigned int index, int value) {
	return sym_max - sym_min + 1 == sym.size() && index >= 0 && index < sym.size() && pos(value) >= sym_min && pos(value) <= sym_max;
}

} /* namespace sym */
