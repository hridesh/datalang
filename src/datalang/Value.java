package datalang;


import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.locks.ReentrantLock;

import datalang.AST.*;

public interface Value {
	public String tostring();
	static class AggregatorVal implements Value {
		private Value _defvalue;
		private List<String> _formals;
		private Exp _body;
		private Env<Value> _body_env;
		private List<List<Value>> _aggregated_values; 
		public AggregatorVal(Value defvalue, List<String> contexts, Exp body, Env<Value> body_env) {
			_defvalue = defvalue;
			_formals = contexts;
			_body = body;
			_body_env = body_env;
			_aggregated_values = new ArrayList<>();
		}
		public Value defvalue() { return _defvalue; }
		public List<String> contexts() { return _formals; }
		public Exp body() { return _body; }
		public Env<Value> aggregator_env() { return _body_env; }
		public List<List<Value>> aggregated_values() { return _aggregated_values; }
		
		public void aggregate(List<Value> aggregated_values){
			_aggregated_values.add(aggregated_values);
		}

		public String tostring() { 
			String result = "(output (";
			for(String formal : _formals) 
				result += formal + " ";
			result += ") ";
			return result + ")";
		}
	}
	static class RefVal extends ReentrantLock implements Value {
		private static final long serialVersionUID = 1L;
		private int _loc = -1; 
		public RefVal(int loc) { _loc = loc; }
		public String tostring() {
			return "loc:" + this._loc;
		}
		public int loc() { return _loc; }
	}
	static class FunVal implements Value { 
		private Env<Value> _env;
		private List<String> _formals;
		private Exp _body;
		public FunVal(Env<Value> env, List<String> formals, Exp body) {
			_env = env;
			_formals = formals;
			_body = body;
		}
		public Env<Value> env() { return _env; }
		public List<String> formals() { return _formals; }
		public Exp body() { return _body; }
		public String tostring() { 
			String result = "(lambda ( ";
			for(String formal : _formals) 
				result += formal + " ";
			result += ") ";
			try {
				result += _body.accept(new Printer.Formatter(), null);
			} catch (ProgramError e) {
				e.printStackTrace();
			}
			return result + ")";
		}
	}
	static class NumVal implements Value {
		private double _val;
		public NumVal(double v) { _val = v; } 
		public double v() { return _val; }
		public String tostring() { 
			int tmp = (int) _val;
			if(tmp == _val) return "" + tmp;
			return "" + _val; 
		}
	}
	static class BoolVal implements Value {
		private boolean _val;
		public BoolVal(boolean v) { _val = v; } 
		public boolean v() { return _val; }
		public String tostring() { if(_val) return "#t"; return "#f"; }
	}
	static class StringVal implements Value {
		private java.lang.String _val;
		public StringVal(String v) { _val = v; } 
		public String v() { return _val; }
		public java.lang.String tostring() { return "" + _val;}
	}
	static class PairVal implements Value {
		protected Value _fst;
		protected Value _snd;
		public PairVal(Value fst, Value snd) { _fst = fst; _snd = snd; } 
		public Value fst() { return _fst; }
		public Value snd() { return _snd; }
		public java.lang.String tostring() { 
			if(isList()) return listToString();
			return "(" + _fst.tostring() + " " + _snd.tostring() + ")"; 
		}
		public boolean isList() {
			if(_snd instanceof Value.Null) return true;
			if(_snd instanceof Value.PairVal &&
					((Value.PairVal) _snd).isList()) return true;
			return false;
		}
		private java.lang.String listToString() {
			String result = "(";
			result += _fst.tostring();
			Value next = _snd; 
			while(!(next instanceof Value.Null)) {
				result += " " + ((PairVal) next)._fst.tostring();
				next = ((PairVal) next)._snd;
			}
			return result + ")";
		}
	}
	static class Null implements Value {
		public Null() {}
		public String tostring() { return "()"; }
	}
	static class UnitVal implements Value {
		public static final UnitVal v = new UnitVal();
		public String tostring() { return ""; }
	}
}
