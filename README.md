Our model was structured by having Sigs represent each of the different characters in Town of Salem. We encoded predicates for each character, describing their normal behaviors they should follow during the game. Additionally, we have a well formed predicate, that dictates the basic structure of how a game of TOS should be played. Every day, we have a pfunc votes_for which tells us which agent each agent voted for, and every night, we have a lone agent who the mafia kills, and a set of people who neutrals killed, although this was a choice we made out of abstraction, but in reality we are only generating traces with 1 neutral killed at most each night. With our model, we are able to prove with a custom initial condition, and various character behavior, whether or not a game of TOW is winnable for a certain group within a set amount of states. 
What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?
One of the fundamental choices we had to make for this project was whether or not we wanted to use temporal mode, or just use the naive ‘states’ implementation, where we use next is linear, like we did before we used temporal mode. On the one hand, since our model was all about modeling action and change over time, we knew that the temporal features could make the model a lot easier. On the other hand, we knew that in our game of Town of Salem, the two state options, days and nights, were completely different types of states. In the nights, most agents wouldn’t do anything while the Mafia and Serial Killer could choose someone to kill. In the day, everyone can vote, which is a completely different action. Because of this massive gap between states, it made sense to us to think of the day and the night as their own Sigs, that each extended the abstract State sig. Additionally, the fact that temporal mode needs an infinite loop, and all TOS games end, temporal mode seemed like it would add unnecessary headaches. In the end, we had a good amount of trouble getting the transitions between states to be correctly constrained in this project, which indicated we might have ended up being better served using temporal mode, and potentially just engineering around the difficulty of that. 
What assumptions did you make about scope? What are the limits of your model?
The entirety of the “Town of Salem” game wasn’t possible to replicate, so we decided to scope the model to its basic elements: a day-night system, a voting system, killing at night, and most crucially, a “Neutral” role system which acts independently and introduces an element of chaos to the game.
We assumed that the game could be balanced and played even without many specialized roles (e.g. Doctor, Mafioso, Godfather, Sheriff) and that the game’s behavior would not shift drastically. We also made the assumption that imperfect recreations of the roles would be enough to create realistic traces— for example, the priority system (which values certain kills over others at Night) was not implemented.
Our model is limited by the integer bit width and the sheer runtime it takes to run longer traces with various roles, and it is also limited by the number of roles and their abilities— for example, the Executioner role is practically the Jester except with a separate target.

Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?
One of our goals for this project was to capture the complexity of Town of Salem. The reason we love that game so much is because it takes the relatively simple game of Mafia and adds a ton of new roles, each of which adds a new wrinkle to the game. While we initially wanted to try to implement a lot of the roles, we found that with too many agents/states, it would take a long time for the model to generate traces, or do any property based testing using unsat or theorem. We also underestimated the complexity of implementing all of these different moving pieces in our model. Just getting our base goal of getting a working game of mafia proved to be more complicated than we anticipated, and with every new role we added, especially the Serial killer, who has a lot of impact over the state transitions, came with its own set of difficulties. When it came time to implement a doctor for example we weren’t able to. Additionally we had dreams of adding some knowledge representation, for example having a medium who could get information from the dead and then use that information to inform their vote, or even to share that information with the rest of the town. This also proved to be beyond the scope of what we were able to do. Additionally, we wanted to have some notion of the stats for the end of the game, for example a sig with a set that contains all the agents who won that trace. This would have allowed some more property testing, ie seeing the maximum, minimum amount of states it takes x people to win, or other interesting properties that involve the total amount of people winning. We were only able to see if different Sigs won, ie if the town won, or if the mafia won. 
How should we understand an instance of your model and what your custom visualization shows?
An instance of our model represents a full trace of a simplified game of Town of Salem. The visualizer is read from top to bottom. The top most rectangle represents the first state in the trace, and the bottom is the last state. The states with a blue background are day states, and the purple states are the night. Inside of each state is a set of circles, each of which represent one of the agents who is alive at the state. The color of the circle tells which type of agent it represents. Green means town, red means mafia, pink means jester, blue means Serial Killer, and gray is executioner. In the day, the black text below the circle is the name of the agent that agent voted for. In the night, the text color of the agent's name represents who is killed that night. Red font means they were killed by the mafia, blue means they were killed by the serial killer, and white means they lived. 


LINK TO VISUALIZER DEMO: https://www.youtube.com/watch?v=FqxXL0qIUqk