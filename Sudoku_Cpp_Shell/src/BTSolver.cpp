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
					changed = true;

					if (n->getDomain().size() == 0)
						return make_pair(assigned, false);

					if (n->getDomain().size() == 1)
					{
						trail->push(n);
						int forcedVal = n->getDomain().getValues()[0];
						n->assignValue(forcedVal);
						assigned[n] = forcedVal;
						changed = true;
					}
				}
			}
		}

		// case 2: if constraint only one place for value -> assign.
		for (Constraint c : network.getConstraints())
		{
			int N = c.vars.size();

			for (int val = 1; val <= N; ++val)
			{
				vector<Variable *> possibleSpots;

				for (Variable *v : c.vars)
				{
					if (v->isAssigned())
					{
						if (v->getAssignment() == val)
						{
							possibleSpots.clear();
							possibleSpots.push_back(v);
							break;
						}
					}
					else if (v->getDomain().contains(val))
					{
						possibleSpots.push_back(v);
					}
				}

				if (possibleSpots.empty())
					return make_pair(assigned, false);

				if (possibleSpots.size() == 1)
				{
					Variable *onlyVar = possibleSpots[0];

					if (!onlyVar->isAssigned())
					{
						trail->push(onlyVar);
						onlyVar->assignValue(val);
						assigned[onlyVar] = val;
						changed = true;
					}
				}
			}
		}

		if (!network.isConsistent())
			return make_pair(assigned, false);
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
	// using norvig + naked pairs as per https://doi.org/10.1051/itmconf/20257004025
    bool changed = true;

    while (changed)
    {
        changed = false;

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
                    changed = true;

                    if (n->getDomain().size() == 0)
                        return false;

                    if (n->getDomain().size() == 1)
                    {
                        trail->push(n);
                        int forcedVal = n->getDomain().getValues()[0];
                        n->assignValue(forcedVal);
                        changed = true;
                    }
                }
            }
        }

        for (Constraint c : network.getConstraints())
        {
            int N = c.vars.size();

            for (int val = 1; val <= N; ++val)
            {
                vector<Variable *> possibleSpots;

                for (Variable *v : c.vars)
                {
                    if (v->isAssigned())
                    {
                        if (v->getAssignment() == val)
                        {
                            possibleSpots.clear();
                            possibleSpots.push_back(v);
                            break;
                        }
                    }
                    else if (v->getDomain().contains(val))
                    {
                        possibleSpots.push_back(v);
                    }
                }

                if (possibleSpots.empty())
                    return false;

                if (possibleSpots.size() == 1 && !possibleSpots[0]->isAssigned())
                {
                    trail->push(possibleSpots[0]);
                    possibleSpots[0]->assignValue(val);
                    changed = true;
                }
            }
        }

        for (Constraint c : network.getConstraints())
        {
            vector<Variable *> candidates;
            for (Variable *v : c.vars)
                if (!v->isAssigned() && v->getDomain().size() == 2)
                    candidates.push_back(v);

            for (int i = 0; i < (int)candidates.size(); ++i)
            {
                for (int j = i + 1; j < (int)candidates.size(); ++j)
                {
                    vector<int> di = candidates[i]->getDomain().getValues();
                    vector<int> dj = candidates[j]->getDomain().getValues();

                    sort(di.begin(), di.end());
                    sort(dj.begin(), dj.end());

                    if (di != dj)
                        continue;

                    int v1 = di[0], v2 = di[1];

                    for (Variable *other : c.vars)
                    {
                        if (other == candidates[i] || other == candidates[j])
                            continue;
                        if (other->isAssigned())
                            continue;

                        bool modified = false;

                        if (other->getDomain().contains(v1))
                        {
                            trail->push(other);
                            other->removeValueFromDomain(v1);
                            modified = true;
                            changed = true;
                        }

                        if (other->getDomain().contains(v2))
                        {
                            if (!modified) trail->push(other);
                            other->removeValueFromDomain(v2);
                            changed = true;
                        }

                        if (other->getDomain().size() == 0)
                            return false;

                        if (other->getDomain().size() == 1)
                        {
                            trail->push(other);
                            int forcedVal = other->getDomain().getValues()[0];
                            other->assignValue(forcedVal);
                            changed = true;
                        }
                    }
                }
            }
        }

        if (!network.isConsistent())
            return false;
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
	int best = INT_MAX;

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
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
    int best_domain = INT_MAX;
    int best_degree = -1;
    vector<Variable*> result;

    for ( Variable* v : network.getVariables() )
    {
        if ( v->isAssigned() )
            continue;

        int domain_size = v->getDomain().size();

        int degree = 0;
        for ( Variable* n : network.getNeighborsOfVariable(v) )
        {
            if ( !n->isAssigned() )
                degree++;
        }

        if ( domain_size < best_domain )
        {
            best_domain = domain_size;
            best_degree = degree;
            result = { v };
        }
        else if ( domain_size == best_domain )
        {
            if ( degree > best_degree )
            {
                best_degree = degree;
                result = { v };
            }
            else if ( degree == best_degree )
            {
                result.push_back( v );
            }
        }
    }

    if ( result.empty() )
        return { nullptr };

    return result;
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable *BTSolver::getTournVar(void)
{
    return MRVwithTieBreaker()[0];
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
