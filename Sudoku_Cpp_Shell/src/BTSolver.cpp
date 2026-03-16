#include "BTSolver.hpp"

using namespace std;

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver(SudokuBoard input, Trail *_trail, string val_sh, string var_sh, string cc)
	: sudokuGrid(input.get_p(), input.get_q(), input.get_board()), network(input)
{
	valHeuristics = val_sh;
	varHeuristics = var_sh;
	cChecks = cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck(void)
{
	for (Constraint c : network.getConstraints())
		if (!c.isConsistent())
			return false;

	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency(void)
{
	vector<Variable *> toAssign;
	vector<Constraint *> RMC = network.getModifiedConstraints();
	for (int i = 0; i < RMC.size(); ++i)
	{
		vector<Variable *> LV = RMC[i]->vars;
		for (int j = 0; j < LV.size(); ++j)
		{
			if (LV[j]->isAssigned())
			{
				vector<Variable *> Neighbors = network.getNeighborsOfVariable(LV[j]);
				int assignedValue = LV[j]->getAssignment();
				for (int k = 0; k < Neighbors.size(); ++k)
				{
					Domain D = Neighbors[k]->getDomain();
					if (D.contains(assignedValue))
					{
						if (D.size() == 1)
							return false;
						if (D.size() == 2)
							toAssign.push_back(Neighbors[k]);
						trail->push(Neighbors[k]);
						Neighbors[k]->removeValueFromDomain(assignedValue);
					}
				}
			}
		}
	}
	if (!toAssign.empty())
	{
		for (int i = 0; i < toAssign.size(); ++i)
		{
			Domain D = toAssign[i]->getDomain();
			vector<int> assign = D.getValues();
			trail->push(toAssign[i]);
			toAssign[i]->assignValue(assign[0]);
		}
		return arcConsistency();
	}
	return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain.
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<unordered_map<Variable *, Domain>, bool> BTSolver::forwardChecking(void)
{
	unordered_map<Variable *, Domain> out;

	for (Variable *var : network.getVariables())
	{
		if (!var->isAssigned())
			continue;

		int val = var->getAssignment();

		for (Variable *n : network.getNeighborsOfVariable(var))
		{
			if (n->isAssigned())
				continue;

			if (n->getDomain().contains(val))
			{
				trail->push(n);
				n->removeValueFromDomain(val);
				out[n] = n->getDomain();

				if (n->getDomain().size() == 0)
					return make_pair(out, false);

				if (n->getDomain().size() == 1)
				{
					trail->push(n);
					vector<int> values = n->getDomain().getValues();
					n->assignValue(values[0]);
					out[n] = n->getDomain();
				}
			}
		}
	}

	return make_pair(out, network.isConsistent());
}

/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned.
 *         The bool is true if assignment is consistent, false otherwise.
 */
pair<unordered_map<Variable *, int>, bool> BTSolver::norvigCheck(void)
{
	unordered_map<Variable *, int> assigned;
	bool changed = true;

	while (changed)
	{
		changed = false;

		// case 1:if var assigned, remove value from neighbors.
		for (Variable *var : network.getVariables())
		{
			if (!var->isAssigned())
			{
				continue;
			}

			int val = var->getAssignment();

			for (Variable *n : network.getNeighborsOfVariable(var))
			{
				if (n->isAssigned())
				{
					continue;
				}

				if (n->getDomain().contains(val))
				{
					trail->push(n);
					n->removeValueFromDomain(val);
					changed = true;

					if (n->getDomain().size() == 0)
					{
						return make_pair(assigned, false);
					}

					if (n->getDomain().size() == 1)
					{
						trail->push(n);

						int val = n->getDomain().getValues()[0];
						n->assignValue(val);
						assigned[n] = val;
						changed = true;
					}
				}
			}
		}

		// case 2: if constraint only one place for value -> assign.
		for (Constraint c : network.getConstraints())
		{
			int N = c.vars.size();

			for (int val = 1; val <= N; val++)
			{
				vector<Variable *> opps;

				for (Variable *v : c.vars)
				{
					if (v->isAssigned())
					{
						if (v->getAssignment() == val)
						{
							opps.clear();
							opps.push_back(v);
							break;
						}
					}
					else if (v->getDomain().contains(val))
					{
						opps.push_back(v);
					}
				}

				if (opps.empty())
				{
					return make_pair(assigned, false);
				}

				if (opps.size() == 1)
				{
					Variable *spot = opps[0];

					if (!spot->isAssigned())
					{
						trail->push(spot);
						spot->assignValue(val);
						assigned[spot] = val;
						changed = true;
					}
				}
			}
		}

		if (!network.isConsistent())
		{
			return make_pair(assigned, false);
		}
	}

	return make_pair(assigned, true);
}

/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */

bool BTSolver::getTournCC(void)
{

	// fc / norvig + naked pairs as per https://doi.org/10.1051/itmconf/20257004025

	//cache everything
	deque<Variable *> worklist;
	for (Variable *v : network.getVariables())
	{
		if (v->isAssigned())
			worklist.push_back(v);
	}

	static unordered_map<Variable *, vector<Variable *>> neighborCache;
	static unordered_map<Variable *, vector<Constraint *>> constraintCache;
	if (neighborCache.empty())
	{
		for (Variable *v : network.getVariables())
		{
			neighborCache[v] = network.getNeighborsOfVariable(v);
			constraintCache[v] = network.getConstraintsContainingVariable(v);
		}
	}


	while (!worklist.empty())
	{
		Variable *curr = worklist.front();
		worklist.pop_front();

		// case 1: Fc if one square got only one val
		int val = curr->getAssignment();
		for (Variable *n : neighborCache[curr])
		{
			if (n->isAssigned())
			{
				if (n->getAssignment() == val)
					return false;
				continue;
			}

			if (n->getDomain().contains(val))
			{
				trail->push(n);
				n->removeValueFromDomain(val);
				if (n->getDomain().size() == 0)
					return false;

				if (n->getDomain().size() == 1)
				{
					trail->push(n);
					n->assignValue(n->getDomain().getValues()[0]);
					worklist.push_back(n);
				}
			}
		}

		// case 2: single choice then naked pair
		for (Constraint *c : constraintCache[curr])
		{

			// 2a. single choice -> assign
			int N = c->vars.size();
			for (int v_idx = 1; v_idx <= N; v_idx++)
			{
				Variable *single = nullptr;
				bool alr_set = false;
				for (Variable *v : c->vars)
				{
					if (v->isAssigned() && v->getAssignment() == v_idx)
					{
						alr_set = true;
						break;
					}
					if (!v->isAssigned() && v->getDomain().contains(v_idx))
					{
						if (single != nullptr)
						{
							single = nullptr;
							break;
						}
						single = v;
					}
				}
				if (!alr_set && single != nullptr)
				{
					trail->push(single);
					single->assignValue(v_idx);
					worklist.push_back(single);
				}
			}

			// 2b. naked pair -> remove from neighbors
			for (int i = 0; i < c->vars.size(); i++)
			{
				Variable *v1 = c->vars[i];
				if (v1->isAssigned() || v1->getDomain().size() != 2)
					continue;

				vector<int> d1 = v1->getDomain().getValues();

				for (int j = i + 1; j < c->vars.size(); j++)
				{
					Variable *v2 = c->vars[j];
					if (v2->isAssigned() || v2->getDomain().size() != 2)
						continue;

					vector<int> d2 = v2->getDomain().getValues();
					if (d1[0] == d2[0] && d1[1] == d2[1])
					{
						// found np
						for (Variable *other : c->vars)
						{
							if (other == v1 || other == v2 || other->isAssigned())
								continue;

							bool changed = false;
							if (other->getDomain().contains(d1[0]))
							{
								trail->push(other);
								other->removeValueFromDomain(d1[0]);
								changed = true;
							}
							if (other->getDomain().contains(d1[1]))
							{
								if (!changed)
									trail->push(other);
								other->removeValueFromDomain(d1[1]);
								changed = true;
							}

							if (changed)
							{
								if (other->getDomain().size() == 0)
									return false;
								if (other->getDomain().size() == 1)
								{
									trail->push(other);
									other->assignValue(other->getDomain().getValues()[0]);
									worklist.push_back(other);
								}
							}
						}
					}
				}
			}
		}
	}
	return true;
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable *BTSolver::getfirstUnassignedVariable(void)
{
	for (Variable *v : network.getVariables())
		if (!(v->isAssigned()))
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable *BTSolver::getMRV(void)
{
	Variable *out = nullptr;
	int best = 2147483642;

	for (Variable *v : network.getVariables())
	{
		if (v->isAssigned())
			continue;

		int curr = v->getDomain().size();
		if (curr < best)
		{
			best = curr;
			out = v;
		}
	}

	return out;
}

/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable *> BTSolver::MRVwithTieBreaker(void)
{
	int best_domain = 2147483642;
	int best_degree = -1;
	vector<Variable *> result;

	for (Variable *v : network.getVariables())
	{
		if (v->isAssigned())
			continue;

		int domain_size = v->getDomain().size();

		int degree = 0;
		for (Variable *n : network.getNeighborsOfVariable(v))
		{
			if (!n->isAssigned())
				degree++;
		}

		if (domain_size < best_domain)
		{
			best_domain = domain_size;
			best_degree = degree;
			result = {v};
		}
		else if (domain_size == best_domain)
		{
			if (degree > best_degree)
			{
				best_degree = degree;
				result = {v};
			}
			else if (degree == best_degree)
			{
				result.push_back(v);
			}
		}
	}

	if (result.empty())
		return {nullptr};

	return result;
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar(void)
{
	// Build neighbor cache once
	unordered_map<Variable*, vector<Variable *>> neighborCache;
	 for (Variable *v : network.getVariables())
		neighborCache[v] = network.getNeighborsOfVariable(v);

	Variable *best = nullptr;
	int best_domain = 2147483642;
	int best_degree = -1;

	for (Variable *v : network.getVariables())
	{
		if (v->isAssigned())
			continue;

		int d = v->getDomain().size();

		// Prune early: can't beat current best on domain
		if (d > best_domain)
			continue;

		int deg = 0;
		for (Variable *n : neighborCache[v])
			if (!n->isAssigned())
				deg++;

		if (d < best_domain || (d == best_domain && deg > best_degree))
		{
			best_domain = d;
			best_degree = deg;
			best = v;
		}
	}

	return best;
}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder(Variable *v)
{
	vector<int> values = v->getDomain().getValues();
	sort(values.begin(), values.end());
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */
vector<int> BTSolver::getValuesLCVOrder(Variable *v)
{
	vector<Variable *> neighbors = network.getNeighborsOfVariable(v);
	vector<pair<int, int>> effects;

	for (int val : v->getDomain().getValues())
	{
		int impact = 0;

		for (Variable *n : neighbors)
		{
			if (!n->isAssigned() && n->getDomain().contains(val))
				impact++;
		}

		effects.push_back(make_pair(val, impact));
	}

	sort(effects.begin(), effects.end(),
		 [](const pair<int, int> &a, const pair<int, int> &b)
		 {
			 return a.second < b.second;
		 });

	vector<int> orderedValues;
	for (const auto &p : effects)
		orderedValues.push_back(p.first);

	return orderedValues;
}

/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal(Variable *v)
{
	// Skip LCV computation if no unassigned neighbors — order irrelevant
	bool unassigned_neighbor = false;
	for (Variable *n : network.getNeighborsOfVariable(v))
	{
		if (!n->isAssigned())
		{
			unassigned_neighbor = true;
			break;
		}
	}

	if (!unassigned_neighbor)
		return getValuesInOrder(v);

	return getValuesLCVOrder(v);
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve(float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
	clock_t begin_clock = clock();

	if (hasSolution)
		return 0;

	// Variable Selection
	Variable *v = selectNextVariable();

	if (v == nullptr)
	{
		for (Variable *var : network.getVariables())
		{
			// If all variables haven't been assigned
			if (!(var->isAssigned()))
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for (int i : getNextValues(v))
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push(v);

		// Assign the value
		v->assignValue(i);

		// Propagate constraints, check consistency, recurse
		if (checkConsistency())
		{
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock) / CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if (check_status == -1)
			{
				return -1;
			}
		}

		// If this assignment succeeded, return
		if (hasSolution)
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency(void)
{
	if (cChecks == "forwardChecking")
		return forwardChecking().second;

	if (cChecks == "norvigCheck")
		return norvigCheck().second;

	if (cChecks == "tournCC")
		return getTournCC();

	return assignmentsCheck();
}

Variable *BTSolver::selectNextVariable(void)
{
	if (varHeuristics == "MinimumRemainingValue")
		return getMRV();

	if (varHeuristics == "MRVwithTieBreaker")
		return MRVwithTieBreaker()[0];

	if (varHeuristics == "tournVar")
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues(Variable *v)
{
	if (valHeuristics == "LeastConstrainingValue")
		return getValuesLCVOrder(v);

	if (valHeuristics == "tournVal")
		return getTournVal(v);

	return getValuesInOrder(v);
}

bool BTSolver::haveSolution(void)
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution(void)
{
	return network.toSudokuBoard(sudokuGrid.get_p(), sudokuGrid.get_q());
}

ConstraintNetwork BTSolver::getNetwork(void)
{
	return network;
}
