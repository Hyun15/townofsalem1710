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
    alive: set Agent,
    next: lone State
}

-- each Day cycle, an Agent can vote for another Agent
-- the Agent that accrues >50% of votes is killed in the Day
sig Day extends State {
    votes_for: pfunc Agent -> Agent
}

-- each Night cycle, a set of Agents can be killed
sig Night extends State {
    mafia_killed: set Agent
    // set Agent: protected
}


pred passiveTownDay[prev: Day, post: Night] {
    all a: Agent | {
        prev.alive
    }
}


pred townLynchBehavior[prev: State, post: State] {

}

pred mafiaPabloEscobarBehavior[]{
    -- everynight, if someone in the mafia is alive, the mafia will kill someone
    all n: Night | {
        some m: Mafia | m in n.alive
        some t: Town | t in n.alive
    } => {
        #{n.mafia_killed} = 1
    }
    -- never vote for the mafia during the day
    all d: Day | {
        no m: Mafia | d.votes_for[m] in Mafia
    }
}

pred mafiaWeirdlyPeacefulBehavior{
--Do nothing during the night
all n: Night | {
    no (n.mafia_killed)
}
-- Never vote for other mafia during the day.
all d: Day | {
        no m: Mafia | d.votes_for[m] in Mafia
    }
}


pred wellformedDay{
    
    all d: Day | {
        -- no one can vote for themselves
        no a: Agent | d.votes_for[a] = a
        -- next is a night state
        some(d.next) => d.next in Night

    }

}

pred wellFormedNight{
    all n: Night | {
        -- mafia cant kill mafia
        no m: Mafia | {
            m in n.mafia_killed
        }
        --next is a day state
       some(n.next) => n.next in Night
    }
}

pred traces{
    wellFormedDay
    wellFormedNight
    all d: Day | {
        -- if someone gets a majority of the votes, then the next stats has that
        -- person gone
        all a: Agent | (#{d.votes_for.a} > add[divide[#{d.alive}, 2],1]) =>{
            some d.next => d.next.alive = d.alive - a
        }

    }
    all n: Night | {
        -- the net days alive it n alive minus mafia killed and whoever else
        some (n.next) => {
            n.next.alive = (n.alive - (n.mafia_killed))
        }

    }

    -- if there is a state that has nothing before it, then it is init
    all s: State | {
        no (next.s) => init[s]
    }
}