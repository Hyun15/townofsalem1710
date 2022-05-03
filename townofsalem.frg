#lang forge/bs1

--------------------------------------------------------------------------------
// AGENTS

-- all players in the game are Agents
abstract sig Agent {}

-- there are three types of Agents: Town, Mafia, and Neutrals
sig Town extends Agent {}
sig Mafia extends Agent {}
sig Neutral extends Agent {} 



-- the Neutral Agents have special win conditions:
sig Jester extends Neutral {}
sig SerialKiller extends Neutral {}
sig Executioner extends Neutral {
    target: one Agent
}

/*
-the Jester wins by being killed during the Day cycle at any point
-the SerialKiller wins by being the only Agent alive at the end
-the Executioner wins if their target is killed while they're alive
*/

--------------------------------------------------------------------------------
// STATES

-- each State represents a day-night shift in the game
abstract sig State {
}

-- each Day cycle, an Agent can vote for another Agent
-- the Agent that accrues >50% of votes is killed in the Day
sig Day extends State {
    votes_for: pfunc Agent -> Agent,
    alive: set Agent,
    next: lone State
}

-- each Night cycle, a set of Agents can be killed
sig Night extends State {
    killed: set Agent,
    alive: set Agent,
    next: lone State
    // set Agent: protected
}


pred passiveTownDay[prev: Day, post: Night] {
    all a: Agent | {
        prev.alive
    }
}


pred townLynchBehavior[prev: State, post: State] {

}