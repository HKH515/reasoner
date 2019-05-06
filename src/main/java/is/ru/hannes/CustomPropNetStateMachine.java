package is.ru.hannes;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
//import org.ggp.base.util.propnet.architecture.Component;
//import org.ggp.base.util.propnet.architecture.PropNet;
//import org.ggp.base.util.propnet.architecture.components.Proposition;
//import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.SimpleMachineState;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;

import is.ru.cadia.ggp.propnet.structure.GGPBasePropNetStructureFactory;
import is.ru.cadia.ggp.propnet.structure.PropNetStructureFactory;
import is.ru.cadia.ggp.propnet.structure.PropNetStructure;
import is.ru.cadia.ggp.propnet.PropNetMove;
import is.ru.cadia.ggp.propnet.structure.components.BaseProposition;
import is.ru.cadia.ggp.propnet.structure.components.StaticComponent;
import is.ru.cadia.ggp.propnet.structure.components.StaticComponent.Type;

import java.io.File;
import java.util.List;
import java.util.BitSet;

import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

import is.ru.cadia.ggp.utils.IOUtils;


@SuppressWarnings("unused")
public class CustomPropNetStateMachine extends StateMachine {
    PropNetStructure structure;

    @Override
    public void initialize(List<Gdl> description) {
        //PropNetStructureFactory factory = new GGPBasePropNetStructureFactory();
        //PropNetStructure structure = factory.create(description);
        PropNetStructureFactory factory = new GGPBasePropNetStructureFactory();
        try {
            structure = factory.create(description);
        }
        catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    public void reason(StaticComponent component, MachineState state) {
        // If we've already computed the value
        if (((CustomMachineState) state).observed(component.id)) {
            return;
        }

        // Base cases
        if (component.type == Type.TRUE) {
            ((CustomMachineState) state).set(component.id, true);
            return;
        }
        else if (component.type == Type.FALSE) {
            ((CustomMachineState) state).set(component.id, false);
            return;
        }
        else if (component.type == Type.PIPE) {
            int predId = component.inputs[0];
            reason(this.structure.getComponent(predId), state);
            ((CustomMachineState) state).set(component.id, ((CustomMachineState) state).get(predId));
            return;
        }
        else if (component.type == Type.NOT) {
            int predId = component.inputs[0];
            reason(this.structure.getComponent(predId), state);
            ((CustomMachineState) state).set(component.id, !((CustomMachineState) state).get(predId));
            return;
        }
        else if (component.type == Type.INPUT) {
            return;
        }
        else if (component.type == Type.INIT) {
            return;
        }
        assert component.type != Type.BASE;

        // Below are cases where there are many input nodes, and not just 1

        Boolean pValue = false;

        // If we're doing an AND, we want it to be true by default, as otherwise it would always be false
        if (component.type == Type.AND) {
            pValue = true;
            for (int predId : component.inputs) {
                StaticComponent pred = this.structure.getComponent(predId);
                reason(pred, state);
                pValue &= ((CustomMachineState) state).get(predId);
            }
            ((CustomMachineState) state).set(component.id, pValue);
            return;
        }
        else if (component.type == Type.OR) {
            for (int predId : component.inputs) {
                StaticComponent pred = this.structure.getComponent(predId);
                reason(pred, state);
                pValue |= ((CustomMachineState) state).get(predId);
            }
            ((CustomMachineState) state).set(component.id, pValue);
            return;
        }
    }

    /**
     * Computes if the state is terminal. Should return the value
     * of the terminal proposition for the state.
     */
    @Override
    public boolean isTerminal(MachineState state) {
        // TODO: Compute whether the MachineState is terminal.
        reason(this.structure.getTerminalProposition(), state);
        return (((CustomMachineState) state).get(this.structure.getTerminalProposition().id));
    }

    /**
     * Computes the goal for a role in the current state.
     * Should return the value of the goal proposition that
     * is true for that role. If there is not exactly one goal
     * proposition true for that role, then you should throw a
     * GoalDefinitionException because the goal is ill-defined.
     */
    @Override
    public int getGoal(MachineState state, Role role)
            throws GoalDefinitionException {
        // TODO: Compute the goal for role in state.
        StaticComponent[] goals = this.structure.getGoalPropositions(this.structure.getRoleId(role));
        int[] goalValues = this.structure.getGoalValues(this.structure.getRoleId(role));
        List<Integer> metGoals = new LinkedList<Integer>();
        for (int i = 0; i < goals.length ; i++) {
            reason(goals[i], state);
            if (((CustomMachineState) state).get(goals[i].id)) {
                metGoals.add(i);
            }
        }
        return goalValues[metGoals.get(0)];
    }

    /**
     * Returns the initial state. The initial state can be computed
     * by only setting the truth value of the INIT proposition to true,
     * and then computing the resulting state.
     */
    @Override
    public MachineState getInitialState() {
        // TODO: Compute the initial state.

        CustomMachineState state = new CustomMachineState(structure);
        for (BaseProposition bp : structure.getBasePropositions()) {
            state.set(bp.id, bp.initialValue);
        }
        
        return state;
    }

    /**
     * Computes the legal moves for role in state.
     */
    @Override
    public List<Move> getLegalMoves(MachineState state, Role role)
            throws MoveDefinitionException {
        // TODO: Compute legal moves.


        MachineState state_clone = state.clone();


        PropNetMove[] moves = this.structure.getPossibleMoves(this.structure.getRoleId(role));
        List<Move> legalMoves = new LinkedList<Move>();
        for (PropNetMove m : moves) {
            reason(m.getLegalComponent(), state_clone);
            if (((CustomMachineState) state_clone).get(m.getLegalComponent().id)) {
                legalMoves.add(m);
            }
            else {
            }
        }
        return legalMoves;
    }

    /**
     * Computes the next state given state and the list of moves.
     */
@Override
public MachineState getNextState(MachineState state, List<Move> moves)
        throws TransitionDefinitionException {
    // We create a clone state of state, as we do not want to mutate state
    CustomMachineState state_clone = new CustomMachineState(this.structure);
    CustomMachineState nextState = new CustomMachineState(this.structure);


    // Set the clone's input components as the same as the original
    for (int i = 0; i < moves.size(); i++) {
        PropNetMove pMove = this.structure.getPropNetMove(i, moves.get(i));
        state_clone.set(pMove.getInputComponent().id, true);
    }

    // Set base propositions of the clone to be the same as the original
    for (BaseProposition bp : this.structure.getBasePropositions()) {
        state_clone.set(bp.id, ((CustomMachineState) state).get(bp.id));
    }

    // This leads to every baseprop being true in nextState
    for (BaseProposition bp : this.structure.getBasePropositions()) {
        // Compute truth value for the base props next component using the state clone
        reason(bp.nextComponent, state_clone);
        // Apply that truth value to the current bitset entry in the next state, as the truth value in the next component in the current bitset
        nextState.set(bp.id, state_clone.get(bp.nextComponent.id));
    }

    return nextState;
}

private CustomMachineState clearInputs(CustomMachineState state) {
    CustomMachineState retState = new CustomMachineState(this.structure);
    for (StaticComponent comp : this.structure.getComponents()) {
        if (comp.type == Type.INPUT) {
            retState.set(comp.id, false);
        }
        else {
            retState.set(comp.id, state.get(comp.id));
        }
    }
    return retState;
}

    @Override
    public List<Role> getRoles() {
        Role[] roles = this.structure.getRoles();
        List<Role> role_list = new LinkedList<Role>();
        for (Role r : roles) {
            role_list.add(r);
        }
        return role_list;
    }

    public static void main(String[] args) throws Exception {
        // setting up the state machine
        String gdlFileName = "/home/hannes/Documents/reasoner/games/games/ticTacToe/ticTacToe.kif";
        String gameDescription = IOUtils.readFile(new File(gdlFileName));
        String preprocessedRules = Game.preprocessRulesheet(gameDescription);
        Game ggpBaseGame = Game.createEphemeralGame(preprocessedRules);
        CustomPropNetStateMachine stateMachine = new CustomPropNetStateMachine(); // insert your own machine here
        stateMachine.initialize(ggpBaseGame.getRules());


        MachineState s0 = stateMachine.getInitialState();
	    List<Move> aJointMove = stateMachine.getLegalJointMoves(s0).get(0);
	    System.out.println("Legal joint moves: " + stateMachine.getLegalJointMoves(s0));
	    System.out.println("Doing move " + aJointMove);
	    MachineState s1 = stateMachine.getNextState(s0, aJointMove);
	    System.out.println(s1);

        List<Move> aJointMove1 = stateMachine.getLegalJointMoves(s1).get(0);
        System.out.println("Legal joint moves: " + stateMachine.getLegalJointMoves(s1));
        System.out.println("Doing move " + aJointMove1);
        MachineState s2 = stateMachine.getNextState(s1, aJointMove1);
        System.out.println(s2);

        List<Move> aJointMove2 = stateMachine.getLegalJointMoves(s2).get(0);
        System.out.println("Legal joint moves: " + stateMachine.getLegalJointMoves(s2));
        System.out.println("Doing move " + aJointMove2);
        MachineState s3 = stateMachine.getNextState(s2, aJointMove2);
        System.out.println(s3);

        List<Move> aJointMove3 = stateMachine.getLegalJointMoves(s3).get(0);
        System.out.println("Legal joint moves: " + stateMachine.getLegalJointMoves(s3));
        System.out.println("Doing move " + aJointMove3);
        MachineState s4 = stateMachine.getNextState(s3, aJointMove3);
        System.out.println(s4);


    }
}