using System;
using System.Collections;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Formatters.Binary;
using ExtraLinq;
using System.Threading.Tasks;


using UltraDES;
using DFA = UltraDES.DeterministicFiniteAutomaton;

using Scheduler = System.Collections.Generic
    .Dictionary<UltraDES.AbstractEvent, float>;

using Restriction = System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, uint>;

using Update = System
    .Func<System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>,
        UltraDES.AbstractEvent,
    System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>
    >;

using TransitionNum = System.Tuple<byte, int>;  // entender seu uso

namespace sequencia_projecao_v10
{
    class PathFinder
    {
        public IEnumerable<List<AbstractEvent>> BFS(                                    // adaptação do BFS para encontrar caminhos entre os nós.             
            AbstractState InitialState,
            AbstractState EndState,
            Dictionary<AbstractState, Transition[]> transicoes
            )
        {
            Queue<List<AbstractState>> InterPath = new Queue<List<AbstractState>>();            // caminho intermediario
            var FinalPaths = new List<List<AbstractState>> { };                                 // armazena todos os caminhos encontrados 
            var CurrPath = new List<AbstractState> { };                                         // armazena o caminho atual
            AbstractState CurrState;
            IEnumerable<AbstractState> ReversePath;
            //var NewPath = new List<AbstractState>() { };

            CurrPath.Add(InitialState);
            InterPath.Enqueue(CurrPath);

            //while (InterPath.Count > 0 && InterPath.All(PathLenght => PathLenght.Count() <= deepth + 1))
            while (InterPath.Count > 0)
            {
                CurrPath = InterPath.Dequeue();
                CurrState = CurrPath.First();
                //Console.Write("{0}\n",aux_path.First());                                      // print debug

                if (CurrState == EndState)                                                      // condição de seleção do 
                {
                    ReversePath = CurrPath.ToArray().Reverse();                                 // O BFS fornece o caminho com a ordem invertida
                    FinalPaths.Add(ReversePath.ToList());
                }
                else
                {
                    foreach (var NextState in transicoes[CurrState].Select(st => st.Destination))   // a apatir do estado atual, vasculha todos os possíveis destinos
                    {
                        if (!CurrPath.Contains(NextState))
                        {
                            var NewPath = new List<AbstractState>() { };
                            //NewPath.Clear();
                            NewPath.Add(NextState);
                            NewPath.AddRange(CurrPath);
                            InterPath.Enqueue(NewPath);
                        }
                    }
                }
            }
            var SeqFinais = BFS_ST2EV(FinalPaths, transicoes);
            return SeqFinais;
        }

        public IEnumerable<List<AbstractEvent>> BFS_ST2EV(                                      // converte a lista de estados visitados em uma lista de eventos 
            IEnumerable<List<AbstractState>> Sequences,
            Dictionary<AbstractState, Transition[]> transitions)
        {
            //var CorEvent = new List<AbstractEvent> { };
            var EVPaths = new List<List<AbstractEvent>> { };
            foreach (var seq in Sequences)
            {                
                var CorEvent = new List<AbstractEvent> { };
                var seqST = seq.ToArray();
                
                for (int i = 0; i < seqST.Length - 1; i++)
                {
                    var evTrans = transitions[seqST[i]].Where(std => std.Destination == seqST[i + 1]).Select(ev => ev.Trigger);
                    CorEvent.Add(evTrans.First());
                }
                EVPaths.Add(CorEvent);
                
            }
            return EVPaths;
        }
    }
}
