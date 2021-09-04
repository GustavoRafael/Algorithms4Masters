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


namespace sequencia_projecao_v10
{
    class FLPClass                                              // Algoritmo de otimização - Escolhe o evento mais frequente
    {
        private static readonly MyRandom Rnd = new MyRandom();

        public (double time, AbstractEvent[] sequency, AbstractState[] dvstate) FullProductionLine(
           int depth,
           Scheduler schSA,
           Restriction resSA,
           Update update,
           AbstractState inicial,
           AbstractState target,
           Dictionary<AbstractState, Transition[]> transitions
           )
        {
            var tempo = 0.0;
            var seq = new List<AbstractEvent>();
            var dstate = new List<AbstractState>();
            var estado = inicial;

            var NxtEv = new Dictionary<AbstractEvent, uint>();

            for (var k = 0; k < depth; k++)
            {
                var trans = transitions[estado].Where(t => t.IsControllableTransition && resSA[t.Trigger] > 0).ToList();

                
                // qdo aparece eventos q modificam o tempo 61,63,65
                if (trans.Any(ts => ts.IsControllableTransition && schSA[ts.Trigger] > 0))
                {
                    var tminSA = transitions[estado]
                        .Where(t => t.IsControllableTransition && resSA[t.Trigger] > 0 && schSA[t.Trigger] > 0 || !t.IsControllableTransition)
                        .Select(t2 => schSA[t2.Trigger])
                        .Min();
                    var transicao1 = transitions[estado].First(t => schSA[t.Trigger] == tminSA);

                    //schSA = update(schSA, transicao1.Trigger);
                    seq.Add(transicao1.Trigger);
                    estado = transicao1.Destination;

                    if (transicao1.Trigger.IsControllable) resSA[transicao1.Trigger]--;

                    continue;
                }

                if (!trans.Any())
                {
                    if (transitions[estado].All(t => t.IsControllableTransition)) break; // se só tem eventos controlaveis (mas não são permitidos)

                    var tmin = transitions[estado].Where(t => !t.IsControllableTransition).Select(t => schSA[t.Trigger]).Min();
                    trans = transitions[estado].Where(t => !t.IsControllableTransition && schSA[t.Trigger] == tmin).ToList();
                    //schSA = update(schSA, trans.Select(ds => ds.Trigger).First());
                    //estado = trans.Select(st => st.Destination).First();
                }

                // armazena os novos estados divergentes
                if (trans.Count > 1 && trans.All(tr => tr.IsControllableTransition))
                {
                    dstate.Add(estado);

                    foreach(var ev in trans.Select(tev=> tev.Trigger))                             // coloca os eventos e suas qtd para a selecao
                    {
                        NxtEv.Add(ev, resSA[ev]);
                    }

                    var EvtSelect = NxtEv.OrderBy(kv => kv.Value).First().Key;                     // 
                    var transicao = trans.Where(ts => ts.Trigger == EvtSelect).First();            // seleciona os eventos ja realizados
                     
                    if (transicao.Trigger.IsControllable) resSA[transicao.Trigger]--;

                    //schSA = update(schSA, transicao.Trigger);
                    seq.Add(transicao.Trigger);
                    estado = transicao.Destination;
                }
                else if (trans.Count == 1 && trans.All(tr => tr.Trigger.IsControllable))
                //else if (trans.Count == 1 && resSA[trans.Select(te => te.Trigger).First()] > 0 && trans.All(tr=> tr.Trigger.IsControllable))
                {
                    var transOne = trans.First();
                    if (transOne.Trigger.IsControllable) resSA[transOne.Trigger]--;

                    //schSA = update(schSA, transOne.Trigger);
                    seq.Add(transOne.Trigger);
                    estado = transOne.Destination;
                }
                else
                {
                    seq.Add(trans.Select(tuc => tuc.Trigger).First());
                    //estado = trans.Select(tuc => tuc.Destination).First();

                    var tmin = transitions[estado].Where(t => !t.IsControllableTransition).Select(t => schSA[t.Trigger]).Min();
                    trans = transitions[estado].Where(t => !t.IsControllableTransition && schSA[t.Trigger] == tmin).ToList();
                    //schSA = update(schSA, trans.Select(ds => ds.Trigger).First());
                    estado = trans.Select(st => st.Destination).First();
                    //estado = trans.Random(Rnd).Destination;
                }
                NxtEv.Clear();                                                                  // limpa o dicionário
            }
            if (estado != inicial) throw new Exception("A busca deve chegar a um estado marcado");

            foreach (var prt in seq)
            {
                //Console.Write($" {prt}");
            }

            return (tempo, seq.Where(e => e.IsControllable).ToArray(), dstate.ToArray());
        }
    }
}
