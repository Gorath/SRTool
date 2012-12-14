package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.ArrayList;
import java.util.List;

public class LoopUnwinderVisitor extends DefaultVisitor {

	private boolean unwindingAssertions;
	private int defaultUnwindBound;

	public LoopUnwinderVisitor(boolean unwindingAssertions,
			int defaultUnwindBound) {
		super(true);
		this.unwindingAssertions = unwindingAssertions;
		this.defaultUnwindBound = defaultUnwindBound;
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
        Stmt whileBody= whileStmt.getBody();

        List<Stmt> statements = new ArrayList<Stmt>();

        // Generate assertions for invariants
        List<Stmt> invariantsAssertions  = generateAssertionsFromInvariants(whileStmt);

        // Generate unwinding assertion and assume
        List<Stmt> unwindingAssertionAndAssume = generateUnwindingAssertionAndAssume(whileStmt);

        // Even if we don't unwind the loop we will assert that the invariants still hold
        statements.addAll(invariantsAssertions);

        // Add the unwinding assertion and assume
        statements.addAll(unwindingAssertionAndAssume);

        // Use default bound if bound provided is null
        int bound = whileStmt.getBound() == null? defaultUnwindBound : whileStmt.getBound().getValue();

        // If we are not unwinding just check all the constraints
        if (bound == 0){
            return convertListOfStatementsToABlockStatement(statements, whileStmt);
        }

        // Unwind the loop as: invariant assertions + if condition + while body
        for (int i = 0; i < bound; i++) {
            List<Stmt> bufferStatements = new ArrayList<Stmt>();

            // Add invariant assertions
            bufferStatements.addAll(invariantsAssertions);

            // Removes unnecessary block statements to make it easier to debug
            removeBlockStatements(bufferStatements, whileBody);

            // Add the previous list of statements
            bufferStatements.addAll(statements);

            // The new if statement contains all the previous statements
            IfStmt ifStatement = new IfStmt(whileStmt.getCondition(), new BlockStmt(bufferStatements) , new EmptyStmt());
            statements.clear();
            statements.add(ifStatement);
        }

        return super.visit(convertListOfStatementsToABlockStatement(statements, whileStmt));
	}

    // Removes unnecessary block statements to make it easier to debug
    private void removeBlockStatements(List<Stmt> statements, Stmt whileBody){
        if (whileBody instanceof  BlockStmt){
            statements.addAll(((BlockStmt) whileBody).getStmtList().getStatements());
        }else{
            statements.add(whileBody);
        }
    }

    // Collates and converts the list of statements to one block statement
    private Stmt convertListOfStatementsToABlockStatement(List<Stmt> statements, Node basedOn){
        if (statements.size() > 1){
            return new BlockStmt(statements, basedOn);
        }
        return statements.get(0);
    }

    // Generates the unwinding assertions and assume
    private List<Stmt> generateUnwindingAssertionAndAssume(WhileStmt whileStmt){
        AssertStmt unwindingAssert = new AssertStmt(new UnaryExpr(UnaryExpr.LNOT,whileStmt.getCondition()),whileStmt);
        AssumeStmt unwindingAssume = new AssumeStmt(new UnaryExpr(UnaryExpr.LNOT,whileStmt.getCondition()));

        List<Stmt> statements = new ArrayList<Stmt>();
        if (unwindingAssertions) {
            statements.add(unwindingAssert);
            statements.add(unwindingAssume);
        } else {
            statements.add(unwindingAssume);
        }
        return  statements;
    }

    // Converts each invariant to an assertion
    private List<Stmt> generateAssertionsFromInvariants(WhileStmt whileStmt){
        List<Stmt> statements = new ArrayList<Stmt>();
        List<Expr> invariantsList = whileStmt.getInvariantList().getExprs();
        for (Expr expression: invariantsList) {
            Stmt assertStmt = new AssertStmt(expression, expression);
            statements.add(assertStmt);
        }
        return statements;
    }
}
