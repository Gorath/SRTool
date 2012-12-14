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

        List<Stmt> statements = new ArrayList<Stmt>();

        // Generate and store a list of statements for the invariant assertions and assumptions
        List<Stmt> invariantAssertions = new ArrayList<Stmt>();
        List<Stmt> invariantAssumptions = new ArrayList<Stmt>();
        generateInvariantAssertionsAndAssumptions(invariantAssertions, invariantAssumptions, whileStmt);

        // Append invariant assertions first
        statements.addAll(invariantAssertions);

        // Find the list of variables that may be modified
        Stmt whileBody = whileStmt.getBody();
        ArrayList<Node> modsetWithDuplicates = whileBody.getModSet();
        ArrayList<DeclRef> modset =  new ArrayList<DeclRef>();

        // Removes duplicate variables found in the modset
        removeDuplicatesInModset(modsetWithDuplicates, modset);

        // Set each of the modified variables to be arbitrary
        // i.e. havoc all the variables in the modset
        List<Stmt> havocs = new ArrayList<Stmt>();
        for (DeclRef variable :modset){
            havocs.add(new HavocStmt(variable));
        }
        statements.addAll(havocs);

        // Append invariant assumptions now that were generated from before
        statements.addAll(invariantAssumptions);

        // Execute loop body once inside an if statement
        List<Stmt> ifBody = new ArrayList<Stmt>();

        // Removes unnecessary block statements to make it easier to debug
        removeBlockStatements(ifBody,whileBody);

        // Append invariant assertions to ensure all the invariants hold before
        // executing the loop body
        ifBody.addAll(invariantAssertions);

        // Assume falsity to prevent any further executions
        ifBody.add(new AssumeStmt(new IntLiteral(0)));

        // Append if statement
        Stmt ifStmt = new IfStmt(whileStmt.getCondition(),new BlockStmt(ifBody),new EmptyStmt(), whileStmt);
        statements.add(ifStmt);

        return super.visit(new BlockStmt(statements,whileStmt));
	}

    // Removes duplicate variables found in the modset
    private void removeDuplicatesInModset(ArrayList<Node> modsetWithDuplicates, ArrayList<DeclRef> modset) {
        for (Node n : modsetWithDuplicates){
            boolean duplicate = false;
            for (Node existing : modset){
                 if (((DeclRef)existing).getName().equals(((DeclRef)n).getName()) ){
                     duplicate = true;
                     break;
                 }
            }
            if (!duplicate) modset.add((DeclRef)n);
        }
    }

    // Removes unnecessary block statements to make it easier to debug
    private void removeBlockStatements(List<Stmt> ifBody, Stmt whileBody) {
        if (whileBody instanceof BlockStmt){
            ifBody.addAll(((BlockStmt)whileBody).getStmtList().getStatements());
        }   else{
            ifBody.add(whileBody);
        }
    }

    // Generate a list of statements for the invariant assertions and assumptions
    private void generateInvariantAssertionsAndAssumptions(List<Stmt> invariantAssertions, List<Stmt> invariantAssumptions, WhileStmt whileStmt){
        ExprList invariantsList = whileStmt.getInvariantList();
        for (Expr expression : invariantsList.getExprs()){
            invariantAssertions.add(new AssertStmt(expression, expression));
            invariantAssumptions.add(new AssumeStmt(expression, expression));
        }
    }

}
