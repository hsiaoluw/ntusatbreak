/*
 * SymmetryGroup.cpp
 *
 *  Created on: Jan 21, 2013
 *      Author: jodv
 */

#include "SymmetryGroup.h"
#include "Symmetry.h"
#include "Translator.h"

namespace sym {

SymmetryGroup::SymmetryGroup(vector<shared_ptr<map<unsigned int, int> > >& syms, shared_ptr<Translator> t)
		: trans(t) {
	if (verbosity > 0) {
		cout << "Creating symmetry group... \n";
	}

	// calculate total support of this group and
	// count the occurrences of literals in input syms (needed to minimize memory footprint)
	set<unsigned int> support;
	unordered_map<unsigned int, unsigned int> literal_occurrences;
	for (auto sym : syms) {
		for (auto paar : *sym) {
			if ((int) paar.first != paar.second) {
				if (support.insert(paar.first).second) {
					literal_occurrences[paar.first] = 0;
				}
				literal_occurrences[paar.first] += 1;
			}
		}
	}
	multimap<unsigned int, unsigned int> sorted_literals;
	for (auto it : support) {
		sorted_literals.insert( { UINT_MAX - literal_occurrences.at(it), it });
	}

	// compress the literals (0 is never used)
	decompression.reserve(support.size() + 1);
	compress(0);
	unordered_map<unsigned int, unsigned int> compression;
	for (auto it : sorted_literals) {
		compression.insert( { it.second, compress(it.second) });
	}
	/*
	 for (auto it : support) {
	 compression.insert({it, compress(it)});
	 }
	 */

	if (verbosity > 0) {
		if (verbosity > 2) {
			for (unsigned int i = 1; i < litUpperBound(); ++i) {
				cout << i << "|" << decompress(i) << endl;
			}
		}
	}
	if (verbosity > 0) {
		unsigned int oldmax = 0;
		unsigned int oldmin = UINT_MAX;
		for (auto m : support) {
			if (m > oldmax)
				oldmax = m;
			if (m < oldmin)
				oldmin = m;
		}
		unsigned int oldsize = (oldmax - oldmin) + 1;
		cout << " percentage of literals compressed: " << (oldsize - litUpperBound() + 1) * 100 / oldsize << "%\n";
		cout << " litUpperBound(): " << litUpperBound() << "\n";
	}

	// create set of generators
	for (auto symMap : syms) {
		unordered_map<unsigned int, int> compressedSym;
		for (auto paar : *symMap) {
			assert(paar.first!=0);
			assert(paar.second!=0);
			unsigned int from = compression.find(paar.first)->second;
			int to = commute(paar.second, compression.find(pos(paar.second))->second);
			assert(from!=0);
			assert(to!=0);
			compressedSym.insert( { from, to });
		}
		generators.insert(make_shared<Symmetry>(compressedSym));
	}

	// fill the sieve needed for prime factorization
	// fill_sieve(litUpperBound());

	if (verbosity > 0) {
		cout << toString();
	}
}

SymmetryGroup::~SymmetryGroup() {
	for (auto columns : columnGroups) {
		for (auto column : *columns) {
			delete column;
		}
		delete columns;
	}

}

string SymmetryGroup::toString() {
	stringstream ss;
	ss << "size=" << getSize() << "|#generators=" << generatorSetSize() << "|#breakingSyms=" << breakingSyms.size() << "\n";
	if (verbosity > 1) {
		ss << "generators: \n";
		for (auto i : generators) {
			ss << sym2string(i, verbosity);
		}
		ss << "breakingSyms: \n";
		for (auto i : breakingSyms) {
			ss << sym2string(i, verbosity);
		}
	}
	return ss.str();
}

unsigned int SymmetryGroup::getSize() {
	unsigned int result = 0;
	for (shared_ptr<Symmetry> s : breakingSyms) {
		result += s->supportSize();
	}
	return result;
}

unsigned int SymmetryGroup::generatorSetSize() {
	return generators.size();
}

void SymmetryGroup::addGenerator(shared_ptr<Symmetry> sym) {
	generators.insert(sym);
}

void SymmetryGroup::generateBreakingConstraint(shared_ptr<Symmetry> sym, vector<int>& order, bool isColumnSym) {
	vector<int> relevantLits;
	sym->calculateUsableLits(relevantLits, order);
	assert(relevantLits.size()>0);
	if (not isColumnSym) {
		assert(sym->getNumberOfSteps()>0);
		relevantLits.resize(sym->getMaxStep() + 1);
	}
	unsigned int currentTseitin;
	unsigned int previousTseitin;

	if (relevantLits.size() > 0) {
		if (verbosity > 2) {
			cout << 0 << ": " << lit2dimacs(decompress(relevantLits[0])) << "->" << lit2dimacs(decompress(sym->symmetrical(relevantLits[0]))) << "\n";
		}
		// add A=>S(A) ->cnf-> ~A | S(A)
		trans->addClause(decompress(neg(relevantLits[0])), decompress(sym->symmetrical(relevantLits[0])));
	}
	if (relevantLits.size() > 1) {
		if (verbosity > 2) {
			cout << 1 << ": " << lit2dimacs(decompress(relevantLits[1])) << "->" << lit2dimacs(decompress(sym->symmetrical(relevantLits[1]))) << "\n";
		}
		// add (A<=>S(A))=>(B=>S(B)) ->cnf-> ~eqT | ~B | S(B)
		currentTseitin = getEquivalenceTseitin(relevantLits[0], sym->symmetrical(relevantLits[0]));
		trans->addClause(neg(currentTseitin), decompress(neg(relevantLits[1])), decompress(sym->symmetrical(relevantLits[1])));
		previousTseitin = currentTseitin;
	}
	for (unsigned int i = 2; i < relevantLits.size(); ++i) { // NOTE: loop only starts at 1
		if (verbosity > 2) {
			cout << i << ": " << lit2dimacs(decompress(relevantLits[i])) << "->" << lit2dimacs(decompress(sym->symmetrical(relevantLits[i]))) << "\n";
		}
		// add (T1 & A<=>S(A))=>(B=>S(B)) ->cnf-> ~T2 | ~B | S(B) && T2 <=> (T1 & A<=>S(A))
		currentTseitin = getConjTseitin(getEquivalenceTseitin(relevantLits[i - 1], sym->symmetrical(relevantLits[i - 1])), previousTseitin);
		trans->addClause(neg(currentTseitin), decompress(neg(relevantLits[i])), decompress(sym->symmetrical(relevantLits[i])));
		previousTseitin = currentTseitin;
	}
}

// NOTE: TSEITINS ARE NEVER COMPRESSED
// => keep this in mind when other compression schemes are used...
void SymmetryGroup::constructSymBreakingFormula() {
	if (verbosity > 0) {
		cout << "Constructing symbreaking formula...\n";
	}
	vector<int> order;

	calculateOrdering(order);

	// check how far each symmetry should be broken
	// note that this methode gives priority to column symmetries,
	// and as a result, symmetries in breakingSyms will be erased
	// when they are made obsolete by column symmetries.

	constructShortestConstraints(order);

	eqTseitins.resize(litUpperBound());
	for (auto sym : breakingSyms) {
		generateBreakingConstraint(sym, order, false);
	}
	for (auto sym : columnSyms) {
		generateBreakingConstraint(sym, order, true);
	}
	for (unsigned int a = 1; a < eqTseitins.size(); ++a) {
		for (auto paar : eqTseitins.at(a)) {
			trans->addEquivalenceDefinition(decompress(a), decompress(paar.first), paar.second);
		}
	}
	for (auto a_paar : conjTseitins) {
		for (auto b_paar : a_paar.second) {
			trans->addConjunctiveDefinition(b_paar.second, a_paar.first, b_paar.first, true);
		}
	}
	/*
	 breakingSyms.clear();
	 columnSyms.clear();
	 */
}

int SymmetryGroup::decompress(int lit) {
	assert(pos(lit)>0);
	assert(pos(lit)<decompression.size());
	return commute(lit, decompression[pos(lit)]);
}

unsigned int SymmetryGroup::compress(unsigned int lit) {
	decompression.push_back(lit);
	return decompression.size() - 1;
}

/*
 * returns true when there was no previous symmetry, so the given symmetry will be added.
 */
void SymmetryGroup::addSym(shared_ptr<Symmetry> inSym) {
	assert(inSym);
	assert(breakingSyms.count(inSym)==0);
	breakingSyms.insert(inSym);
}

void SymmetryGroup::eraseSym(shared_ptr<Symmetry> inSym) {
	assert(inSym);
	assert(breakingSyms.count(inSym)!=0);
	breakingSyms.erase(inSym);
}

unsigned int SymmetryGroup::litUpperBound() {
	return decompression.size();
}

void SymmetryGroup::constructShortestConstraints(vector<int>& order) {
	// For each lit-var pair, the best (least preconditions) symmetry mapping var to lit, along with the number of preconditions
	unordered_map<int, unordered_map<int, pair<shared_ptr<Symmetry>, unsigned int> > > bestConstraints;

	for (auto sym : columnSyms) {
		sym->findBetterConstraints(bestConstraints, order);
	}
	for (auto sym : breakingSyms) {
		sym->findBetterConstraints(bestConstraints, order);
	}
	vector<shared_ptr<Symmetry> > uselessSyms;
	for (auto sym : breakingSyms) {
		if (sym->getNumberOfSteps() == 0) {
			uselessSyms.push_back(sym);
		}
	}
	for (auto sym : uselessSyms) {
		assert( breakingSyms.count(sym) !=0);
		eraseSym(sym);
	}
	if (verbosity > 0) {
		cout << "Symmetries removed by constructing shortest constraints: " << uselessSyms.size() << "\n";
		printStats();
	}
}

void SymmetryGroup::printStats() {
	unsigned int avgSteps = 0;
	unsigned int avgMaxStep = 0;
	for (auto sym : breakingSyms) {
		avgSteps += sym->getNumberOfSteps();
		avgMaxStep += sym->getMaxStep();
	}
	if (verbosity > 1) {
		cout << "*** PRINTING STATS ***\n";
		cout << "avgSteps: " << avgSteps / breakingSyms.size() << ", avgMaxStep: " << avgMaxStep / breakingSyms.size() << endl;
	}
}

int SymmetryGroup::getEquivalenceTseitin(int a, int b) {
	assert(a!=0 && b!=0);
	bool sameSign = (sign(a) && sign(b)) || (not sign(a) && not sign(b));
	a = pos(a);
	b = pos(b);
	assert(a!=b);
	if (a > b) {
		unsigned int tmp = a;
		a = b;
		b = tmp;
	}
	assert(a<(int) eqTseitins.size());
	unsigned int tseitin;
	if (eqTseitins[a].count(b) == 0) {
		tseitin = trans->getNext();
		eqTseitins[a][b] = tseitin;
	} else {
		tseitin = eqTseitins[a][b];
	}
	if (sameSign) {
		return tseitin;
	} else {
		return neg(tseitin);
	}
}

unsigned int SymmetryGroup::getConjTseitin(int a, int b) {
	assert(a!=0);
	assert(b!=0);
	assert(a!=b);
	if (a < b) {
		unsigned int tmp = a;
		a = b;
		b = tmp;
	}
	if (conjTseitins.count(a) && conjTseitins[a].count(b)) {
		return conjTseitins[a][b];
	}
	unsigned int tseitin = trans->getNext();
	conjTseitins[a][b] = tseitin;
	return tseitin;
}

bool SymmetryGroup::isValidOrdering(vector<int>& ordering) {
	assert(ordering.size() == 2 * litUpperBound() - 2);
	// note: assert(ordering.size() == 2 * litUpperBound() - 2); is not always true if symmetries get removed between calculation of orderings.
	unordered_set<int> lits;
	lits.insert(ordering.cbegin(), ordering.cend());
	for (unsigned int i = 0; i < ordering.size(); i += 2) {
		assert(ordering.at(i)==neg(ordering.at(i+1)));
	}
	assert(lits.size()==ordering.size());
	return true;
}

void SymmetryGroup::getImage(int lit, vector<int>& partialOrder, unordered_set<int>& result, unordered_set<int>& specialLits,
		vector<shared_ptr<Symmetry> >& syms) {
	result.clear();
	for (unsigned int i = 0; i < syms.size(); ++i) {
		if (not syms.at(i)->overlapsWith(partialOrder)) {
			int symLit = syms.at(i)->symmetrical(lit);
			if (symLit != lit && specialLits.count(symLit) == 0) {
				result.insert(symLit);
			}
		} else {
			syms[i] = syms.back();
			syms.pop_back();
			--i;
		}
	}
}

int getSmallest(unordered_set<int>& toPick, unordered_map<unsigned int, unsigned int>& ranking) {
	assert(ranking.size()>0);
	unsigned int min = UINT_MAX;
	int currentBest = ranking.cbegin()->first;
	for (auto lit : toPick) {
		if (ranking.at(pos(lit)) < min) {
			min = ranking.at(pos(lit));
			currentBest = lit;
		}
	}
	return currentBest;
}

// result[i] gives the set of symmetries for which the symmetrical(partialorder[2*i])!=partialorder[2*i], and there is no such smaller i.
// symmetries which are disjunct with the total ordering are ignored
void levelOfSyms(vector<shared_ptr<Symmetry> >& syms, vector<int>& partialorder, vector<vector<shared_ptr<Symmetry> > >& result) {
	result.clear();
	for (unsigned int j = 0; j < partialorder.size(); j += 2) {
		int lit = partialorder.at(j);
		result.push_back(vector<shared_ptr<Symmetry> >());
		for (unsigned int i = 0; i < syms.size(); ++i) {
			if (syms.at(i)->symmetrical(lit) != lit) {
				result.back().push_back(syms.at(i));
				syms[i] = syms.back();
				syms.pop_back();
				--i;
			}
		}
		if (syms.size() == 0) {
			return;
		}
	}
}

void SymmetryGroup::eraseEmbeddedSyms() {
	if (verbosity > 0) {
		cout << "Erasing embedded syms..." << endl;
	}
	unsigned int initialSize = breakingSyms.size();
	// create set of literals which can not be a candidate to insert in the partial order
	for (auto cgroup : columnGroups) {
		unordered_set<int> forbiddenLits;
		for (auto column : *cgroup) {
			for (auto lit : *column) {
				forbiddenLits.insert(lit);
				forbiddenLits.insert(neg(lit));
			}
		}
		vector<shared_ptr<Symmetry> > toErase;
		for (auto sym : breakingSyms) {
			if (sym->supportIsSubset(forbiddenLits)) {
				toErase.push_back(sym);
			}
		}
		for (auto sym : toErase) {
			breakingSyms.erase(sym);
		}
	}
	if (verbosity > 0) {
		cout << "percentage of breakingSyms embedded in columnGroups: " << (initialSize - breakingSyms.size()) * 100 / initialSize << endl;
	}
}

// This is a hack to get a reasonable ordering.
void SymmetryGroup::calculateOrdering(vector<int>& result) {
	if (verbosity > 0) {
		cout << "Calculating order..." << endl;
	}
	result.clear();

	// create set of literals which can not be a candidate to insert in the partial order
	unordered_set<int> forbiddenLits;
	for (auto cgroup : columnGroups) {
		for (auto column : *cgroup) {
			for (auto lit : *column) {
				forbiddenLits.insert(lit);
				forbiddenLits.insert(neg(lit));
			}
		}
	}

	vector<shared_ptr<Symmetry> > currentSyms;
	for (auto sym : breakingSyms) {
		if (not sym->supportIsSubset(forbiddenLits)) {
			currentSyms.push_back(sym);
		}
	}

	if (currentSyms.size() > 0) {
		// count the occurrences
		unordered_map<unsigned int, unsigned int> literal_occurrences;
		for (auto sym : currentSyms) {
			for (unsigned int i = 0; i < sym->supportSize(); ++i) {
				unsigned int lit = sym->get(i);
				if (literal_occurrences.count(lit) == 0) {
					literal_occurrences[lit] = 0;
				}
				literal_occurrences[lit] = literal_occurrences.at(lit) + 1;
			}
		}

		vector<int> currentOrder;
		vector<vector<int> > connectedLits; // given the current ordering, a constraint connectedLit[i][j] => connectedLit[i][j+1] will be generated
		unordered_set<int> toPick;
		for (unsigned int lit = 1; lit < litUpperBound(); ++lit) {
			if (forbiddenLits.count(lit) == 0) {
				toPick.insert(lit);
				toPick.insert(neg(lit));
			}
		}

		int smallest = getSmallest(toPick, literal_occurrences);
		unordered_set<int> image;
		getImage(smallest, currentOrder, image, forbiddenLits, currentSyms);

		while (image.size() > 0) { // if the image is empty given the current ordering, it will stay empty since the order will only be extended
			connectedLits.push_back(vector<int>());
			connectedLits.back().push_back(smallest);
			currentOrder.push_back(smallest);
			currentOrder.push_back(neg(smallest));
			toPick.erase(smallest);
			toPick.erase(neg(smallest));

			while (image.size() > 0) {

				smallest = getSmallest(image, literal_occurrences);
				getImage(smallest, currentOrder, image, forbiddenLits, currentSyms);
				connectedLits.back().push_back(smallest);
				currentOrder.push_back(smallest);
				currentOrder.push_back(neg(smallest));
				toPick.erase(smallest);
				toPick.erase(neg(smallest));
			}
			smallest = getSmallest(toPick, literal_occurrences);
			getImage(smallest, currentOrder, image, forbiddenLits, currentSyms);
		}

		// sorting the remaining literals based on their occurrences
		multimap<unsigned int, unsigned int> tmpMap;
		for (auto lit : toPick) {
			if (not sign(lit)) {
				tmpMap.insert( { literal_occurrences.at(pos(lit)), pos(lit) });
			}
		}
		// add remaining literals to currentOrder
		for (auto litpair : tmpMap) {
			currentOrder.push_back(litpair.second);
			currentOrder.push_back(neg(litpair.second));
		}
		if (verbosity > 0) {
			cout << "connectedLits.size(): " << connectedLits.size() << endl;
			for (unsigned int i = 0; i < connectedLits.size(); ++i) {
				if (connectedLits.at(i).size() > 1) {
					for (auto lit : connectedLits.at(i)) {
						cout << lit << ", ";
					}
					cout << endl;
				}
			}
		}

		unordered_set<int> usedLiterals;
		for (auto lit : currentOrder) {
			if (usedLiterals.insert(lit).second) { // check needed to avoid double literals in resulting order, due to inverting symmetries
				result.push_back(lit);
			}
		}

	}

	for (auto cgroup : columnGroups) {
		for (auto column : *cgroup) {
			for (auto lit : *column) {
				result.push_back(lit);
				result.push_back(neg(lit));
			}
		}
	}

	if (verbosity > 1) {
		cout << "resulting order: ";
		for (auto lit : result) {
			cout << lit << ", ";
		}
		cout << endl;
	}
	assert(isValidOrdering(result));
}

// post: input keeps only symmetries which can still form disjunct related sym sets
bool SymmetryGroup::extractOneRelatedSymSet(vector<shared_ptr<Symmetry> >& input, vector<vector<int>*>* columnGroup) {
	if (input.size() == 0) {
		return false;
	}
	assert(columnGroup->size()==0);
	// generate a related sym set with only two syms
	for (int i = input.size() - 1; i >= 0; --i) {
		for (unsigned int j = 0; j < input.size() - 1; ++j) {
			input.back()->getColumns(input.at(j), columnGroup);
			if (columnGroup->size() == 3) {
				input[j] = input.back();
				input.pop_back();
				break;
			}
		}
		input.pop_back();
		if (columnGroup->size() == 3) {
			break;
		}
	}
	if (columnGroup->size() != 3) {
		return false;
	}
	// else: try to extend
	if (verbosity > 0) {
		cout << "trying to extend..." << endl;
	}
	for (auto sym : input) {
		sym->extendColumns(columnGroup);
	}
	if (verbosity > 1) {
		for (auto col : *columnGroup) {
			for (auto lit : *col) {
				cout << lit << ", ";
			}
			cout << endl;
		}
	}
	return true;
}

void SymmetryGroup::extractRelatedSymSets(set<shared_ptr<Symmetry>, classcomp>& inSyms, vector<vector<vector<int>*>*>& outSyms) {
	assert(outSyms.size()==0);
	map<unsigned int, vector<shared_ptr<Symmetry> >*> groups; // order involutions by support
	for (auto sym : inSyms) {
		if (sym->isInvolution()) {
			if (groups.count(sym->supportSize()) == 0) {
				groups.insert( { sym->supportSize(), new vector<shared_ptr<Symmetry> >() });
			}
			groups[sym->supportSize()]->push_back(sym);
		}
	}

	for (auto group_pair : groups) {
		if (verbosity > 0) {
			cout << "Current group support size: " << group_pair.first << " [" << group_pair.second->size() << "]\n";
		}
		bool found = true;
		while (found) {
			vector<vector<int>*>* tmp = new vector<vector<int>*>();
			found = extractOneRelatedSymSet(*(group_pair.second), tmp);
			if (found) {
				unordered_set<int> totalLits;
				for (auto column : *tmp) {
					for (auto lit : *column) {
						totalLits.insert(lit);
					}
				}
				outSyms.push_back(tmp);
				for (auto pair_it2 : groups) {
					removeOverlappingSyms(totalLits, *(pair_it2.second));
				}
				if (verbosity > 0) {
					cout << "Found columnGroup with " << tmp->size() << " columns of length " << tmp->at(0)->size() << endl;
				}
			}

		}
	}
	for (auto group_pair : groups) {
		delete group_pair.second;
	}
}

/*
 * lengths[x][y]
 * 1. nothing if composition x after y has not yet been calculated
 * 2. UINT_MAX if composition x after y already is part of the set of compositions
 * 3. an int representing the length of composition x after y if it has already been calculated, but not yet added
 */
void SymmetryGroup::calcLength(shared_ptr<Symmetry> first, shared_ptr<Symmetry> second, unsigned int& maxLength,
		set<shared_ptr<Symmetry>, classcomp>& compositions, unordered_map<shared_ptr<Symmetry>, unordered_map<shared_ptr<Symmetry>, unsigned int> >& lengths,
		vector<shared_ptr<Symmetry> >& newlyAdded) {
	shared_ptr<Symmetry> candidate = NULL;
	unsigned int currentLength = UINT_MAX;
	if (lengths.at(first).count(second) == 0) {
		if (first->isDisjunctWith(second)) {
			// this symmetry will be split into its two components again, so avoiding double work
			lengths.at(first)[second] = UINT_MAX;
			lengths.at(second)[first] = UINT_MAX;
			return;
		}
		// composition has not been calculated yet. Do so.
		candidate = first->after(second);
		if (candidate->isIdentity()) {
			lengths.at(first)[second] = UINT_MAX;
			return;
		}

		currentLength = candidate->supportSize();
		if (currentLength > maxLength) {
			lengths.at(first)[second] = currentLength;
			candidate = NULL;
		} else {
			lengths.at(first)[second] = UINT_MAX;
		}
	} else {
		currentLength = lengths.at(first).at(second);
		if (currentLength <= maxLength) {
			lengths.at(first)[second] = UINT_MAX;
			candidate = first->after(second);
		}
	}
	if (candidate != NULL && compositions.insert(candidate).second) {
		maxLength = currentLength;
		newlyAdded.push_back(candidate);
		lengths[candidate] = unordered_map<shared_ptr<Symmetry>, unsigned int>();
	}
}

bool containsIdentity(set<shared_ptr<Symmetry>, classcomp>& syms) {
	shared_ptr<Symmetry> identity = make_shared<Symmetry>();
	return syms.count(identity) > 0;
}

bool timeLimitReached(time_t& startTime, unsigned int timeLimit) {
	time_t endTime;
	time(&endTime);
	return difftime(endTime, startTime) > timeLimit;
}

void SymmetryGroup::extractSmallSymmetries(vector<shared_ptr<Symmetry> >& oldSyms, set<shared_ptr<Symmetry>, classcomp>& compositions, unsigned int index) {
	assert(compositions.size()==0);
	unsigned int maxLength = 0;
	unordered_map<shared_ptr<Symmetry>, unordered_map<shared_ptr<Symmetry>, unsigned int> > lengths; // of calculated compositions, as well as a bool stating whether the composition is splittable
	for (auto sym : oldSyms) {
		compositions.insert(sym);
		lengths[sym] = unordered_map<shared_ptr<Symmetry>, unsigned int>();
	}

	double timeLimit = ((double) maxTime - usedTime) / (double) (nrSymGroups - index);
	vector<shared_ptr<Symmetry> > toTest;
	vector<shared_ptr<Symmetry> > newlyAdded;
	if (verbosity > 0) {
		cout << "Max mem: " << maxMemory << "\n";
		cout << "Time limit: " << timeLimit << "\n";
		cout << "Start amount: " << compositions.size() << endl;
	}
	time_t startTime;
	time(&startTime);
	while (maxLength != UINT_MAX - 1 && maxMemory > getPhysicalValue(compositions.size(), litUpperBound()) && not timeLimitReached(startTime, timeLimit)) {
		maxLength = UINT_MAX - 1;
		for (auto comp : compositions) {
			toTest.push_back(comp);
		}

		while (toTest.size() > 0 && (maxMemory > getPhysicalValue(compositions.size(), litUpperBound()) && not timeLimitReached(startTime, timeLimit))) {
			for (auto test : toTest) {
				if (maxMemory <= getPhysicalValue(compositions.size(), litUpperBound()) || timeLimitReached(startTime, timeLimit)) {
					break;
				}
				for (auto old : oldSyms) { // NOTE: do not change this to compositions, you will be adding while in a loop :(
					if (timeLimitReached(startTime, timeLimit)) {
						break;
					}
					calcLength(test, old, maxLength, compositions, lengths, newlyAdded);
					calcLength(old, test, maxLength, compositions, lengths, newlyAdded);
				}
			}
			toTest.clear();
			for (auto newly : newlyAdded) {
				toTest.push_back(newly);
			}
			newlyAdded.clear();
			if (verbosity > 0) {
				cout << maxLength << "[" << compositions.size() << "] ";
			}
		}
		if (verbosity > 0) {
			cout << flush;
		}
	}
	if (verbosity > 0) {
		cout << endl;
	}
	time_t endTime;
	time(&endTime);
	usedTime += difftime(endTime, startTime);
	cout << "c final mem: " << getPhysicalValue(compositions.size(), litUpperBound()) << endl;
	assert(not containsIdentity(compositions));

}

void SymmetryGroup::checkForRelatedSyms(unsigned int index) {
	// creating compositions:
	// stop criterium: no more compositions can be found, or the number of compositions reaches a treshold based on memory capacity
	//set<shared_ptr<Symmetry> , classcomp> compositions;
	assert(breakingSyms.size()==0);
	set<shared_ptr<Symmetry>, classcomp> compositions;
	vector<shared_ptr<Symmetry> > oldSyms;
	for (auto generator : generators) {
		oldSyms.push_back(generator);
	}
	if (verbosity > 0) {
		cout << "Calculating small symmetries..." << endl;
	}
	extractSmallSymmetries(oldSyms, compositions, index);
	// taking only the binary ones for further related syms calculation
	set<shared_ptr<Symmetry>, classcomp> binaryComps;
	for (auto comp : compositions) {
		if (comp->isInvolution()) {
			binaryComps.insert(comp);
		}
		assert(breakingSyms.count(comp)==0);
		addSym(comp);
		// adding all symmetries to the generator set for further breaking
	}

	assert(columnGroups.size()==0);
	if (verbosity > 0) {
		cout << "Extracting relevant column groups..." << endl;
	}
	extractRelatedSymSets(binaryComps, columnGroups);

	if (verbosity > 1) {
		for (auto columns : columnGroups) {
			cout << "Number of columns: " << columns->size() << endl;
			for (auto column : *columns) {
				for (auto lit : *column) {
					cout << lit2dimacs(decompress(lit)) << " ";
				}
				cout << "\n";
			}
			cout << flush;
		}
	}

	// adding syms from columngroups to breakingsyms
	// NOTE: adding one sym too many, so the order doesn't matter when breaking these syms
	for (auto cgroup : columnGroups) {
		for (unsigned int index = 0; index < cgroup->size(); ++index) {
			unsigned int next = (index + 1) % cgroup->size();
			assert(cgroup->at(index)->size()==cgroup->at(next)->size());
			unordered_map<unsigned int, int> values;
			for (unsigned int j = 0; j < cgroup->at(index)->size(); ++j) {
				int lit = cgroup->at(index)->at(j);
				int sym_lit = cgroup->at(next)->at(j);
				values.insert( { pos(lit), commute(lit, sym_lit) });
				values.insert( { pos(sym_lit), commute(sym_lit, lit) });
			}
			columnSyms.push_back(make_shared<Symmetry>(values));
		}
	}
}

string SymmetryGroup::sym2string(shared_ptr<Symmetry> s, unsigned int verb) {
	stringstream ss;
	ss << " Support? " << s->supportSize() << " Involution? " << s->isInvolution() << "\n";
	if (verb > 1) {
		stringstream firstline;
		stringstream secondline;
		for (unsigned int i = 0; i < s->supportSize(); ++i) {
			unsigned int lit = s->get(i);
			firstline << lit2dimacs(decompress(lit)) << "|";
			secondline << lit2dimacs(decompress(s->symmetrical(lit))) << "|";
		}
		ss << firstline.str() << "\n" << secondline.str() << "\n";
	}
	return ss.str();
}

} /* namespace sym */
