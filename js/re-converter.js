class convert2RE {
    constructor(fa) {
        if (fa.start === null || !Object.keys(fa.states).includes(fa.start)) {
            throw new NoStartPointError();
        }
        if (!fa.hasAnyTerminalState()) {
            throw new NoTerminalStateError();
        }
        if (fa.isGeneralizedFa()) {
            throw new AlreadyConvertedToREError();
        }

        // cloning new fa from originFA
        this.fa = new FiniteAutomata();
        this.fa.import(fa.export());
    }

    buildTransitionTable(fa) {
        const transitionTable = {};
    
        for (const state of Object.values(fa.states)) {
            transitionTable[state.name] = {};
    
            for (const symbol in state.transitions) {
                const destinations = state.transitions[symbol];
                transitionTable[state.name][symbol] = destinations.join('+');
            }
        }
    
        return transitionTable;
    }
    
    transitiveClosure(state, transitionTable) {
        const visited = new Set();
        const queue = [state];
        const regex = [];
    
        while (queue.length > 0) {
            const current = queue.shift();
            visited.add(current);
    
            const transitions = transitionTable[current];
            const transitionRegexes = [];
    
            for (const symbol in transitions) {
                const destinations = transitions[symbol].split('+');
                const destinationRegexes = destinations.map(dest => {
                    if (visited.has(dest)) {
                        return dest;
                    } else {
                        queue.push(dest);
                        return this.transitiveClosure(dest, transitionTable);
                    }
                });
    
                transitionRegexes.push(`(${destinationRegexes.join('+')})${symbol === '' ? '' : symbol}`);
            }
    
            regex.push(`(${transitionRegexes.join('+')})${current !== state ? '*' : ''}`);
        }
    
        return regex.join('');
    }

    /**
     * Converts a FA to RegularExpression in three steps:
     *
     * Step 1:
     *  Remove trap state if it exists (if fa is deterministic)
     *
     * Step 2:
     *  A:
     *      Add new start state and make a λ transition to former start states
     *  B:
     *      Add new terminal state and make λ transitions from all terminal states to new terminal state
     *      and make all terminal states to non-terminal states except new terminal states
     *
     * Step 3:
     *  While count fa's states is greater than 2 repeat :
     *      find a state which has minimum number of transitions, as currentState
     *      iterate over all transitions of sates that has transition to current state and merge them with current state's transitions
     *      remove current state from fa
     *
     */
    run() {
        const { fa } = this;

        // Step 1: Remove trap state if it exists (if fa is deterministic)
        if (Object.values(fa.states).some(state => state.name.trim() === '')) {
            fa.removeState('');
        }

        // Step 2: Create a new start state with lambda transitions to the original start states
        let newStartState = {
            name: 'λ',
            x: 0,
            y: 0,
            transitions: {
                '': [fa.start],
            },
        };
        fa.addState(newStartState);
        fa.start = newStartState.name;

        // Step 3: Convert FA to regular expression using transitive closure method
        const transitionTable = this.buildTransitionTable(fa);
        const regex = this.transitiveClosure(fa.start, transitionTable);

        return regex;
    }

    /**
     * Merges same transitions of a state
     * Same transitions are transitions that have same source and destination states with different transition symbol
     *
     * @example
     * before :
     *          state transitions : {'a':['1','2'], 'b':['3'], 'c':['1','2']}
     * After :
     *          state transitions : {'a,c':['1','2'], 'b':['3']}
     *
     */
    mergeSameTransitionsOf(state) {
        for (let transitionOneSymbol in state.transitions) {
            if (!state.transitions.hasOwnProperty(transitionOneSymbol)) continue;
            let transitionOne = state.transitions[transitionOneSymbol];

            for (let transitionTwoSymbol in state.transitions) {
                if (!state.transitions.hasOwnProperty(transitionTwoSymbol)) continue;
                let transitionTwo = state.transitions[transitionTwoSymbol];

                if (!transitionOne || !transitionTwo || transitionOneSymbol === transitionTwoSymbol) {
                    continue;
                }
                if (transitionOne.length === transitionTwo.length && transitionOne.every(stateName => transitionTwo.includes(stateName))) {
                    state.transitions[
                        '(' +
                            (transitionOneSymbol.trim().length === 0 ? 'λ' : transitionOneSymbol) +
                            '+' +
                            (transitionTwoSymbol.trim().length === 0 ? 'λ' : transitionTwoSymbol) +
                            ')'
                    ] = state.transitions[transitionOneSymbol];
                    delete state.transitions[transitionOneSymbol];
                    delete state.transitions[transitionTwoSymbol];
                }
            }
        }
    }

    /**
     * Get symbols of all transitions that source state and destination state is this state
     * in other words return symbols of all star transitions of this state
     * @param {State} state
     * @returns {Array} Array of symbols of all star transitions
     */
    getSymbolsOfTransitionToItself(state) {
        let result = [];
        for (let transitionSymbol in state.transitions) {
            if (!state.transitions.hasOwnProperty(transitionSymbol)) continue;
            let transition = state.transitions[transitionSymbol];

            if (transition.includes(state.name)) {
                state.transitions[transitionSymbol] = state.transitions[transitionSymbol].filter(st => st !== state.name);
                result.push(transitionSymbol);
            }
        }
        return result;
    }

    /**
     * Get next state for Step 3 of @see convert2RE
     * @param {FiniteAutomata} fa
     * @returns {State}
     */
    getNextState(fa) {
        let result,
            minTransitionCount = 0;
        for (let name in fa.states) {
            const state = fa.states[name];
            if (!state || fa.start === name || state.terminal) {
                continue;
            }

            let statesHasTransitionFromState = [];
            for (let transitionName in state.transitions) {
                const transition = state.transitions[transitionName];
                if (transition === undefined) continue;
                statesHasTransitionFromState = [...new Set(transition.concat(statesHasTransitionFromState))];
            }
            if (minTransitionCount == 0 || (statesHasTransitionFromState.length != 0 && statesHasTransitionFromState.length < minTransitionCount)) {
                minTransitionCount = statesHasTransitionFromState.length;
                result = state;
            }
        }
        return result;
    }

    /**
     * Get all states that has transition to state
     * @param {State} state destination state
     * @returns {Array} Array of states that has transition to state
     */
    getStatesHasTransitionTo(state) {
        const { fa } = this;
        let result = [];

        for (let originState of fa.states) {
            if (this.isAnyTransitionBetween(originState, state)) {
                result.push(originState);
            }
        }

        return [...new Set(result)];
    }

    /**
     * Check if there is any transition between two states
     * @param {State} from Source state
     * @param {State} to Destination state
     *
     * @returns {Boolean} Returns true if there is any transition otherwise returns false
     */
    isAnyTransitionBetween(from, to) {
        for (let transition of Object.values(from.transitions)) {
            if (transition.includes(to.name)) return true;
        }
        return false;
    }

    /**
     * Get all terminal states of fa
     * @param {FiniteAutomata} fa
     * @returns {Array} Array of terminal states
     */
    getTerminalStates(fa) {
        return Object.values(fa.states).filter(state => state.terminal);
    }
}
