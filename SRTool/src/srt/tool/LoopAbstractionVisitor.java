package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.ArrayList;
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
        Stmt[] invAssert = new Stmt[numOfInvariants];
        Stmt[] invAssume = new Stmt[numOfInvariants];

        for (int i = 0; i < numOfInvariants; i++) {
            Expr e = invariantsList.getExprs().get(i);
            Stmt assertStmt = new AssertStmt(e,e);
            Stmt assumeStmt = new AssumeStmt(e,e);
            invAssert[i] = assertStmt;
            invAssume[i] = assumeStmt;
        }

        Stmt invariantAssertions = new BlockStmt(invAssert);

        returnStatement = new BlockStmt(new Stmt[]{invariantAssertions});

        /**********************************************/
        /************       Havoc modset       ********/
        /*********************************************/

        Stmt whileBody = whileStmt.getBody();
        ArrayList<Node> modset = whileBody.getModSet();

        //************************** REMOVE DUPLICATES?? **********************/

        Stmt[] stmts = new Stmt[modset.size()];
        for (int i = 0; i < modset.size(); i++){
            Stmt havocMod = new HavocStmt((DeclRef)modset.get(i),whileStmt);
            stmts[i] = havocMod;
        }

        returnStatement = new BlockStmt(new Stmt[]{returnStatement,new BlockStmt(stmts)});


        /**********************************************/
        /************   Assume the invariants  ********/
        /*********************************************/

         returnStatement = new BlockStmt(new Stmt[] {returnStatement,new BlockStmt(invAssume)});

        /**********************************************/
        /************  Execute loop body once  ********/
        /*********************************************/

        Stmt ifbody = new BlockStmt(new Stmt[]{whileBody,new BlockStmt(invAssert),new AssumeStmt(new IntLiteral(0))});

        Stmt ifStmt = new IfStmt(whileStmt.getCondition(),ifbody,new EmptyStmt(), whileStmt);

        returnStatement = new BlockStmt(new Stmt[] {returnStatement,ifStmt},whileStmt);


        /**********************************************/
        /************        Done              ********/
        /*********************************************/


        return super.visit(returnStatement);


	}

    //private Node[] getModSet(Node n) {

    //}

}
