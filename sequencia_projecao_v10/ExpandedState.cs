using System;
using UltraDES;

namespace sequencia_projecao_v10
{
    [Serializable]
    class ExpandedState:State
    {
        public uint Tasks { get; private set; }

        public ExpandedState(string alias, uint tasks, Marking marking = Marking.Unmarked)
            : base(alias, marking)
        {
            Tasks = tasks;
        }

        public override AbstractState ToMarked
        {
            get
            {
                return IsMarked ? this : new ExpandedState(Alias, Tasks, Marking.Marked);
            }
        }

        public override AbstractState ToUnmarked
        {
            get
            {
                return !IsMarked ? this : new ExpandedState(Alias, Tasks, Marking.Unmarked);
            }
        }

        public override bool Equals(object obj)
        {
            if (ReferenceEquals(this, obj)) return true;

            // If parameter cannot be cast to Point return false.
            var p = obj as State;
            if ((Object)p == null) return false;

            // Return true if the fields match:
            return Alias == p.Alias && Marking == p.Marking;
        }

        public override int GetHashCode()
        {
            return Alias.GetHashCode();
        }

        public override string ToString()
        {
            return Alias;
        }
    }
}
