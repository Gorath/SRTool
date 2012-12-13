package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.List;

public class LoopAbstractionVisitor extends DefaultVisitor {

	public LoopAbstractionVisitor() {
		super(true);
	}

	@Override
	public Object visit(WhileStmt whileStmt) {

        Stmt returnStatement;

        /**********************************************/
        /************ Assert of all invariants ********/
        /*********************************************/

        ExprList invariantsList = whileStmt.getInvariantList();
        int numOfInvariants = invariantsList.getExprs().size();
        Stmt[] invStmts = new Stmt[numOfInvariants];

        for (int i = 0; i < numOfInvariants; i++) {
            Expr e = invariantsList.getExprs().get(i);
            Stmt assertStmt = new AssertStmt(e,e);
            invStmts[i] = assertStmt;
        }

        Stmt invariantAssertions = new BlockStmt(invStmts);

        returnStatement = new BlockStmt(new Stmt[]{invariantAssertions});

        /**********************************************/
        /************       Havoc modset       ********/
        /*********************************************/

        Stmt whileBody = whileStmt.getBody();
        List<Node> whileChildren = whileBody.getChildrenCopy();


        /**********************************************/
        /************   Assume the invariants  ********/
        /*********************************************/



        /**********************************************/
        /************  Execute loop body once  ********/
        /*********************************************/



        /**********************************************/
        /************        Done              ********/
        /*********************************************/




		return super.visit(whileStmt);
	}

    //private Node[] getModSet(Node n) {

    //}

}
