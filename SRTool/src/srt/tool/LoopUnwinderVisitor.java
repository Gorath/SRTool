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

        //these are the statements produced by this method.
        List<Stmt> statements = new ArrayList<Stmt>();

        List<Stmt> invariants  = generateAssertionsFromInvariants(whileStmt);
        List<Stmt> loopEnd = generateLoopEnd(whileStmt);

        //even if we don't unwind the loop we will assert that the invariants still hold
        //and reason about the unwinding depth.
        statements.addAll(invariants);
        statements.addAll(loopEnd);

        //use default bound if bound provided is null
        int bound = whileStmt.getBound() == null? defaultUnwindBound : whileStmt.getBound().getValue();


        //if we are not unwinding just check all the constraints.
        if (bound == 0){
            return convertListToStatement(statements,whileStmt);
        }

        //unwind the loop as:
        // invariants + while body
        for (int i = 0; i < bound; i++) {
            List<Stmt> tmp = new ArrayList<Stmt>();
            tmp.addAll(invariants);
            removeBlockStatements(tmp, whileBody);
            tmp.addAll(statements);
            IfStmt ifStmt = new IfStmt(whileStmt.getCondition(), new BlockStmt(tmp) , new EmptyStmt());
            //the new ifstatement consumes all  the previous statements.
            statements.clear();
            statements.add(ifStmt);
        }

        return super.visit( convertListToStatement(statements,whileStmt));
	}

    private void removeBlockStatements(List<Stmt> statements, Stmt whileBody){
        //removes unecessary block statments... final output looks nicer
        //although predication and SSA destroy it later.. but easier to debug.
        if ( whileBody instanceof  BlockStmt){
            statements.addAll(((BlockStmt) whileBody).getStmtList().getStatements());
        }else{
            statements.add(whileBody);
        }
    }

    //there should be atleast one statement.
    private static Stmt convertListToStatement(List<Stmt> statements, Node basedOn){
        if (statements.size() > 1){
            return new BlockStmt(statements,basedOn);
        }
        return  statements.get(0);
    }

    //this method generates the last assertions or assume for unwinding
    private List<Stmt> generateLoopEnd(WhileStmt whileStmt){

        AssertStmt loopAssert = new AssertStmt(new UnaryExpr(UnaryExpr.LNOT,whileStmt.getCondition()),whileStmt);
        AssumeStmt loopAssume = new AssumeStmt(new UnaryExpr(UnaryExpr.LNOT,whileStmt.getCondition()));

        List<Stmt> statements = new ArrayList<Stmt>();
        if (unwindingAssertions) {
            statements.add(loopAssert);
            statements.add(loopAssume);
        } else {
            statements.add(loopAssume);
        }
        return  statements;
    }

    // this method converts each invariant to an assertion
    private  List<Stmt> generateAssertionsFromInvariants(WhileStmt whileStmt){
        List<Stmt> statements = new ArrayList<Stmt>();
        List<Expr> invariantsList = whileStmt.getInvariantList().getExprs();
        for (Expr expression: invariantsList) {
            Stmt assertStmt = new AssertStmt(expression,expression);
            statements.add(assertStmt);
        }
        return  statements;

    }
}
