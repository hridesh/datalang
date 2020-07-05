package datalang;

import java.util.ArrayList;
import java.util.List;

/**
 * This class hierarchy represents expressions in the abstract syntax tree
 * manipulated by this interpreter.
 * 
 * @author hridesh
 * 
 */
public interface AST {
	public static abstract class ASTNode implements AST {
		public abstract <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError;
	}
	public static class Program extends ASTNode {
		List<DefineDecl> _decls;
		Exp _e;

		public Program(List<DefineDecl>decls, Exp e) {
			_decls = decls;
			_e = e;
		}

		public Exp e() {
			return _e;
		}
		
		public List<DefineDecl> decls() {
			return _decls;
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}
	
	@SuppressWarnings("serial")
	public static class ProgramError extends Exception {
		public ProgramError(String message) {
			super(message);
		}
	}

	public static abstract class Exp extends ASTNode {

	}

	public static class VarExp extends Exp {
		String _name;

		public VarExp(String name) {
			_name = name;
		}

		public String name() {
			return _name;
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	public static class UnitExp extends Exp {
		
		public UnitExp() {}

		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}

	}

	public static class NumExp extends Exp {
		double _val;

		public NumExp(double v) {
			_val = v;
		}

		public double v() {
			return _val;
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	public static class StrExp extends Exp {
		String _val;

		public StrExp(String v) {
			_val = v;
		}

		public String v() {
			return _val;
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	public static class BoolExp extends Exp {
		boolean _val;

		public BoolExp(boolean v) {
			_val = v;
		}

		public boolean v() {
			return _val;
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	public static abstract class CompoundArithExp extends Exp {
		List<Exp> _rest;

		public CompoundArithExp() {
			_rest = new ArrayList<Exp>();
		}

		public CompoundArithExp(Exp fst) {
			_rest = new ArrayList<Exp>();
			_rest.add(fst);
		}

		public CompoundArithExp(List<Exp> args) {
			_rest = new ArrayList<Exp>();
			for (Exp e : args)
				_rest.add((Exp) e);
		}

		public CompoundArithExp(Exp fst, List<Exp> rest) {
			_rest = new ArrayList<Exp>();
			_rest.add(fst);
			_rest.addAll(rest);
		}

		public CompoundArithExp(Exp fst, Exp second) {
			_rest = new ArrayList<Exp>();
			_rest.add(fst);
			_rest.add(second);
		}

		public Exp fst() {
			return _rest.get(0);
		}

		public Exp snd() {
			return _rest.get(1);
		}

		public List<Exp> all() {
			return _rest;
		}

		public void add(Exp e) {
			_rest.add(e);
		}
		
	}

	public static class AddExp extends CompoundArithExp {
		public AddExp(Exp fst) {
			super(fst);
		}

		public AddExp(List<Exp> args) {
			super(args);
		}

		public AddExp(Exp fst, List<Exp> rest) {
			super(fst, rest);
		}

		public AddExp(Exp left, Exp right) {
			super(left, right);
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	public static class SubExp extends CompoundArithExp {

		public SubExp(Exp fst) {
			super(fst);
		}

		public SubExp(List<Exp> args) {
			super(args);
		}

		public SubExp(Exp fst, List<Exp> rest) {
			super(fst, rest);
		}

		public SubExp(Exp left, Exp right) {
			super(left, right);
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	public static class DivExp extends CompoundArithExp {
		public DivExp(Exp fst) {
			super(fst);
		}

		public DivExp(List<Exp> args) {
			super(args);
		}

		public DivExp(Exp fst, List<Exp> rest) {
			super(fst, rest);
		}

		public DivExp(Exp left, Exp right) {
			super(left, right);
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	public static class MultExp extends CompoundArithExp {
		public MultExp(Exp fst) {
			super(fst);
		}

		public MultExp(List<Exp> args) {
			super(args);
		}

		public MultExp(Exp fst, List<Exp> rest) {
			super(fst, rest);
		}

		public MultExp(Exp left, Exp right) {
			super(left, right);
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}
	
	/**
	 * A let expression has the syntax 
	 * 
	 *  (let ((name expression)* ) expression)
	 *  
	 * @author hridesh
	 *
	 */
	public static class LetExp extends Exp {
		List<String> _names;
		List<Exp> _value_exps; 
		Exp _body;
		
		public LetExp(List<String> names, List<Exp> value_exps, Exp body) {
			_names = names;
			_value_exps = value_exps;
			_body = body;
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
		
		public List<String> names() { return _names; }
		
		public List<Exp> value_exps() { return _value_exps; }

		public Exp body() { return _body; }

	}
	
	/**
	 * A define declaration has the syntax 
	 * 
	 *  (define name expression)
	 *  
	 * @author hridesh
	 *
	 */
	public static class DefineDecl extends Exp {
		String _name;
		Exp _value_exp; 
		
		public DefineDecl(String name, Exp value_exp) {
			_name = name;
			_value_exp = value_exp;
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
		
		public String name() { return _name; }
		
		public Exp value_exp() { return _value_exp; }

	}
	
	/**
	 * An anonymous procedure declaration has the syntax
	 * 
	 * @author hridesh
	 *
	 */
	public static class LambdaExp extends Exp {		
		List<String> _formals;
		Exp _body;
		
		public LambdaExp(List<String> formals, Exp body) {
			_formals = formals;
			_body = body;
		}
		
		public List<String> formals() { return _formals; }
		
		public Exp body() { return _body; }
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}
	
	/**
	 * A call expression has the syntax
	 * 
	 * @author hridesh
	 *
	 */
	public static class CallExp extends Exp {
		Exp _operator; 
		List<Exp> _operands;
		
		public CallExp(Exp operator, List<Exp> operands) {
			_operator = operator; 
			_operands = operands;
		}
		
		public Exp operator() { return _operator; }

		public List<Exp> operands() { return _operands; }
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	/**
	 * An if expression has the syntax
	 * 
	 * (if conditional_expression true_expression false_expression)
	 * 
	 * @author hridesh
	 *
	 */
	public static class IfExp extends Exp {
		Exp _conditional; 
		Exp _then_exp; 
		Exp _else_exp; 
		
		public IfExp(Exp conditional, Exp then_exp, Exp else_exp) {
			_conditional = conditional;
			_then_exp = then_exp; 
			_else_exp = else_exp; 
		}
		
		public Exp conditional() { return _conditional; }
		public Exp then_exp() { return _then_exp; }
		public Exp else_exp() { return _else_exp; }
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}
	
	/**
	 * A less expression has the syntax
	 * 
	 * ( < first_expression second_expression )
	 * 
	 * @author hridesh
	 *
	 */
	public static class LessExp extends BinaryComparator {
		public LessExp(Exp first_exp, Exp second_exp) {
			super(first_exp, second_exp);
		}
				
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}
	
	public static abstract class BinaryComparator extends Exp {
		private Exp _first_exp; 
		private Exp _second_exp; 
		BinaryComparator(Exp first_exp, Exp second_exp) {
			_first_exp = first_exp;
			_second_exp = second_exp; 
		}
		public Exp first_exp() { return _first_exp; }
		public Exp second_exp() { return _second_exp; }
	}

	/**
	 * An equal expression has the syntax
	 * 
	 * ( == first_expression second_expression )
	 * 
	 * @author hridesh
	 *
	 */
	public static class EqualExp extends BinaryComparator {
		public EqualExp(Exp first_exp, Exp second_exp) {
			super(first_exp, second_exp);
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	/**
	 * A greater expression has the syntax
	 * 
	 * ( > first_expression second_expression )
	 * 
	 * @author hridesh
	 *
	 */
	public static class GreaterExp extends BinaryComparator {
		public GreaterExp(Exp first_exp, Exp second_exp) {
			super(first_exp, second_exp);
		}
				
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	/**
	 * A car expression has the syntax
	 * 
	 * ( car expression )
	 * 
	 * @author hridesh
	 *
	 */
	public static class CarExp extends Exp {
		private Exp _arg; 
		public CarExp(Exp arg){
			_arg = arg;
		}
		public Exp arg() { return _arg; }
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}
	
	/**
	 * A cdr expression has the syntax
	 * 
	 * ( car expression )
	 * 
	 * @author hridesh
	 *
	 */
	public static class CdrExp extends Exp {
		private Exp _arg; 
		public CdrExp(Exp arg){
			_arg = arg;
		}
		public Exp arg() { return _arg; }
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}
	
	/**
	 * A cons expression has the syntax
	 * 
	 * ( cons expression expression )
	 * 
	 * @author hridesh
	 *
	 */
	public static class ConsExp extends Exp {
		private Exp _fst; 
		private Exp _snd; 
		public ConsExp(Exp fst, Exp snd){
			_fst = fst;
			_snd = snd;
		}
		public Exp fst() { return _fst; }
		public Exp snd() { return _snd; }
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	/**
	 * A list expression has the syntax
	 * 
	 * ( list expression* )
	 * 
	 * @author hridesh
	 *
	 */
	public static class ListExp extends Exp {
		private List<Exp> _elems; 
		public ListExp(List<Exp> elems){
			_elems = elems;
		}
		public List<Exp> elems() { return _elems; }
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}
	
	/**
	 * A null expression has the syntax
	 * 
	 * ( null? expression )
	 * 
	 * @author hridesh
	 *
	 */
	public static class NullExp extends Exp {
		private Exp _arg; 
		public NullExp(Exp arg){
			_arg = arg;
		}
		public Exp arg() { return _arg; }
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

    public static class IsBooleanExp extends Exp {
    	private Exp e;
    	public IsBooleanExp(Exp e){
    		this.e=e;
    	}
    	Exp exp(){
    		return this.e;
    	}
    	public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
    		return visitor.visit(this, env);
    	}
    }
    
    public static class IsNumberExp extends Exp {
    	private Exp e;
    	public IsNumberExp(Exp e){
    		this.e=e;
    	}
    	Exp exp(){
    		return this.e;
    	}
    	public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
    		return visitor.visit(this, env);
    	}
    }
    
    public static class IsStringExp extends Exp {
    	private Exp e;
    	public IsStringExp(Exp e){
    		this.e=e;
    	}
    	Exp exp(){
    		return this.e;
    	}
    	public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
    		return visitor.visit(this, env);
    	}
    }
    
    public static class IsProcedureExp extends Exp {
    	private Exp e;
    	public IsProcedureExp(Exp e){
    		this.e=e;
    	}
    	Exp exp(){
    		return this.e;
    	}
    	public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
    		return visitor.visit(this, env);
    	}
    }
    
    public static class IsUnitExp extends Exp {
    	private Exp e;
    	public IsUnitExp(Exp e){
    		this.e=e;
    	}
    	Exp exp(){
    		return this.e;
    	}
    	public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
    		return visitor.visit(this, env);
    	}
    }
    
    public static class IsPairExp extends Exp {
    	private Exp e;
    	public IsPairExp(Exp e){
    		this.e=e;
    	}
    	Exp exp(){
    		return this.e;
    	}
    	public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
    		return visitor.visit(this, env);
    	}
    }
    
    public static class IsListExp extends Exp {
    	private Exp e;
    	public IsListExp(Exp e){
    		this.e=e;
    	}
    	Exp exp(){
    		return this.e;
    	}
    	public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
    		return visitor.visit(this, env);
    	}
    }

    public static class IsNullExp extends Exp {
    	private Exp e;
    	public IsNullExp(Exp e){
    		this.e=e;
    	}

    	Exp exp(){
    		return this.e;
    	}
    	public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
    		return visitor.visit(this, env);
    	}
    }

	/**
	 * Eval expression: evaluate the program that is _val
	 * @author hridesh
	 *
	 */
	public static class EvalExp extends Exp {
		private Exp _code; 
		public EvalExp(Exp code){
			_code = code;
		}
		public Exp code() { return _code; }
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	/**
	 * Read expression: reads the file that is _file
	 * @author hridesh
	 *
	 */
	public static class ReadExp extends Exp {
		private Exp _file; 
		public ReadExp(Exp file){
			_file = file;
		}
		public Exp file() { return _file; }
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	/**
	 * A letrec expression has the syntax 
	 * 
	 *  (letrec ((name expression)* ) expression)
	 *  
	 * @author hridesh
	 *
	 */
	public static class LetrecExp extends Exp {
		List<String> _names;
		List<Exp> _fun_exps; 
		Exp _body;
		
		public LetrecExp(List<String> names, List<Exp> fun_exps, Exp body) {
			_names = names;
			_fun_exps = fun_exps;
			_body = body;
		}
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
		
		public List<String> names() { return _names; }
		
		public List<Exp> fun_exps() { return _fun_exps; }

		public Exp body() { return _body; }

	}

    /**
     * A ref expression has the syntax 
     * 
     *  (ref expression)
     *  
     * @author hridesh
     *
     */
    public static class RefExp extends Exp {
            private Exp _value_exp;

            public RefExp(Exp value_exp) {
                    _value_exp = value_exp;
            }

            public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
                    return visitor.visit(this, env);
            }

            public Exp value_exp() { return _value_exp; }

    }

    /**
     * A deref expression has the syntax 
     * 
     *  (deref expression)
     *  
     * @author hridesh
     *
     */
    public static class DerefExp extends Exp {
            private Exp _loc_exp;

            public DerefExp(Exp loc_exp) {
                    _loc_exp = loc_exp;
            }

            public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
                    return visitor.visit(this, env);
            }

            public Exp loc_exp() { return _loc_exp; }

    }

    /**
     * An assign expression has the syntax 
     * 
     *  (set! expression expression)
     *  
     * @author hridesh
     *
     */
    public static class AssignExp extends Exp {
            private Exp _lhs_exp;
            private Exp _rhs_exp;

            public AssignExp(Exp lhs_exp, Exp rhs_exp) {
                    _lhs_exp = lhs_exp;
                    _rhs_exp = rhs_exp;
            }

            public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
                    return visitor.visit(this, env);
            }

            public Exp lhs_exp() { return _lhs_exp; }
            public Exp rhs_exp() { return _rhs_exp; }

    }

    /**
     * A free expression has the syntax 
     * 
     *  (free expression)
     *  
     * @author hridesh
     *
     */
    public static class FreeExp extends Exp {
            private Exp _value_exp;

            public FreeExp(Exp value_exp) {
                    _value_exp = value_exp;
            }

            public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
                    return visitor.visit(this, env);
            }

            public Exp value_exp() { return _value_exp; }

    }


    /**
     * An emit expression has the syntax 
     * 
     *  (<< aggregator expression+)
     *  
     * @author hridesh
     *
     */
	public static class EmitExp extends Exp {
		Exp _aggregator; 
		List<Exp> _actuals;
		
		public EmitExp(Exp event, List<Exp> actuals) {
			_aggregator = event; 
			_actuals = actuals;
		}
		
		public Exp aggregator() { return _aggregator; }

		public List<Exp> actuals() { return _actuals; }
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	
    /**
     * An aggregator expression has the syntax 
     * 
     *  (aggregator (Identifier+) expression)
     *  
     * @author hridesh
     *
     */
	public static class AggregatorExp extends Exp {
		Exp _defvalue;
		Exp _body;
		List<String> _contexts;
		
		public AggregatorExp(Exp defvalue, List<String> contexts, Exp body) {
			_defvalue = defvalue;
			_body = body;
			_contexts = contexts;
		}
		
		public Exp body() { return _body; }
		public List<String> contexts() { return _contexts; }
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	/**
	 * A job expression has the syntax 
	 * 
	 *  (job aggregator* expression)
	 *  
	 */
	public static class JobExp extends Exp {
		Exp _input;
		List<String> _names;
		List<Exp> _aggregators;
		Exp _body;
		
		public JobExp(Exp input, List<String> names, List<Exp> aggregators, Exp body) {
			_input = input;
			_names = names;
			_aggregators = aggregators;
			_body = body;
		}
		
		public Exp input() { return _input; }
		public List<String> names() { return _names; }
		public List<Exp> aggregators() { return _aggregators; }
		public Exp body() { return _body; }
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}

	/**
	 * A print expression has the syntax 
	 * 
	 *  (print expression*)
	 *  
	 */
	public static class PrintExp extends Exp {
		private List<Exp> _expressions;

		public PrintExp(List<Exp> expressions) {
			_expressions = expressions; 
		}

		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}

		public List<Exp> expressions() { return _expressions; }

	}
	
	/**
	 * A seq expression has the syntax
	 * 
	 * (seq exp0 exp1 exp2 ..)
	 * 
	 * @author hridesh
	 *
	 */
	public static class SeqExp extends Exp {
		private List<Exp> _expressions;
		
		public SeqExp(List<Exp> expressions) {
			_expressions = expressions; 
		}
		
		public List<Exp> expressions() { return _expressions; }
		
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}


	public static class ErrorExp extends Exp {
		public <T,U> T accept(Visitor<T,U> visitor, Env<U> env) throws ProgramError {
			return visitor.visit(this, env);
		}
	}
	
	public interface Visitor <T, U> {
		// This interface should contain a signature for each concrete AST node.
		public T visit(AST.AddExp e, Env<U> env) throws ProgramError;
		public T visit(AST.UnitExp e, Env<U> env) throws ProgramError;
		public T visit(AST.NumExp e, Env<U> env) throws ProgramError;
		public T visit(AST.StrExp e, Env<U> env) throws ProgramError;
		public T visit(AST.BoolExp e, Env<U> env) throws ProgramError;
		public T visit(AST.DivExp e, Env<U> env) throws ProgramError;
		public T visit(AST.ErrorExp e, Env<U> env) throws ProgramError;
		public T visit(AST.MultExp e, Env<U> env) throws ProgramError;
		public T visit(AST.Program p, Env<U> env) throws ProgramError;
		public T visit(AST.SubExp e, Env<U> env) throws ProgramError;
		public T visit(AST.VarExp e, Env<U> env) throws ProgramError;
		public T visit(AST.LetExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.DefineDecl d, Env<U> env) throws ProgramError; 
		public T visit(AST.ReadExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.EvalExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.LambdaExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.CallExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.LetrecExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.IfExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.LessExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.EqualExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.GreaterExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.CarExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.CdrExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.ConsExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.ListExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.NullExp e, Env<U> env) throws ProgramError; 
        public T visit(AST.IsNullExp e, Env<U> env) throws ProgramError; 
        public T visit(AST.IsProcedureExp e, Env<U> env) throws ProgramError; 
        public T visit(AST.IsListExp e, Env<U> env) throws ProgramError; 
        public T visit(AST.IsPairExp e, Env<U> env) throws ProgramError; 
        public T visit(AST.IsUnitExp e, Env<U> env) throws ProgramError; 
        public T visit(AST.IsNumberExp e, Env<U> env) throws ProgramError; 
        public T visit(AST.IsStringExp e, Env<U> env) throws ProgramError; 
        public T visit(AST.IsBooleanExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.RefExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.DerefExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.AssignExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.FreeExp e, Env<U> env) throws ProgramError;
		public T visit(AST.AggregatorExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.EmitExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.JobExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.PrintExp e, Env<U> env) throws ProgramError; 
		public T visit(AST.SeqExp e, Env<U> env) throws ProgramError; 
	}	
}
