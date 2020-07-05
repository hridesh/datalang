package datalang;

import datalang.AST.ProgramError;

/**
 * Representation of a heap, which maps references to values.
 * 
 * @author hridesh
 *
 */
public interface Heap {

	Value ref (Value value) throws ProgramError;

	Value deref (Value.RefVal loc) throws ProgramError;

	Value setref (Value.RefVal loc, Value value) throws ProgramError;

	Value free (Value.RefVal value) throws ProgramError;

	static public class Heap16Bit implements Heap {
		static final int HEAP_SIZE = 65_536;
		
		Value[] _rep = new Value[HEAP_SIZE];
		int index = 0;
		
		public Value ref (Value value) throws ProgramError {
			if(index >= HEAP_SIZE)
				throw new ProgramError("Out of memory error");
			Value.RefVal new_loc = new Value.RefVal(index);
			_rep[index++] = value;
			return new_loc;
		}

		public Value deref (Value.RefVal loc) throws ProgramError {
			try {
				return _rep[loc.loc()];
			} catch (ArrayIndexOutOfBoundsException e) {
				throw new ProgramError("Segmentation fault at access " + loc);
			}
		}

		public Value setref (Value.RefVal loc, Value value) throws ProgramError {
			try {
				return _rep[loc.loc()] = value;
			} catch (ArrayIndexOutOfBoundsException e) {
				throw new ProgramError("Segmentation fault at access " + loc);
			}
		}

		public Value free (Value.RefVal loc) throws ProgramError {
			try {
				_rep[loc.loc()] = null;
				//REMARK: students should add this location to free list.
				return loc;
			} catch (ArrayIndexOutOfBoundsException e) {
				throw new ProgramError("Segmentation fault at access " + loc);
			}
		}

		public Heap16Bit(){}
	}

}
