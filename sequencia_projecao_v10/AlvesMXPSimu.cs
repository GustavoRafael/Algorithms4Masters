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

using MathNet.Numerics.Statistics;

using Scheduler = System.Collections.Generic
    .Dictionary<UltraDES.AbstractEvent, float>;

using Restriction = System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, uint>;

using Update = System
    .Func<System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>,
        UltraDES.AbstractEvent,
    System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>
    >;

using TimeContext = System.Tuple<sequencia_projecao_v10
    .SinglyLinkedList<UltraDES.AbstractEvent>,
    System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>,
    System.Collections.Generic.Dictionary
    <UltraDES.AbstractEvent, uint>,
    float>;
using TransitionNum = System.Tuple<byte, int>;  // entender seu uso

namespace sequencia_projecao_v10
{
    // GU-Comment: Todos os testes do Lucas estão agrupados aki 
    class AlvesMXPSimu
    {
        public void AllMXP()
        {
            float maxIt = 3;

            // GU-Comment: carrega o problema  ser resolvido (SFM, SF, ITL) 
            ISchedulingProblem plant = new SFM();

            var transitions = plant.Supervisor.Transitions.AsParallel()
                .GroupBy(t => t.Origin)
                .ToDictionary(gr => gr.Key, gr => gr.ToArray());
#if DEBUG

            var collisions = transitions.Keys
                .Select(k => k.GetHashCode())
                .GroupBy(h => h)
                .Select(ge => ge.Count())
                .Max();
            Debug.WriteLine($"Max collisions on transitions: {collisions}");

#endif
            sequencia_projecao_v10.ClassMXP mxp = new ClassMXP();

            Func<int, AbstractEvent[]>[] tests = new Func<int, AbstractEvent[]>[5];

            //Logical Algorithms

            tests[1] = (prod) => mxp.GreedyParallelism(
                plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                plant.Depth * prod,
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(prod),
                transitions
                ).ToArray();

            tests[0] = (prod) => mxp.LogicalMaximumParallelism(
                plant.Supervisor,
                plant.InitialState,
                plant.Depth * prod,
                plant.TargetState,
                plant.InitialRestrition(prod),
                transitions
                ).ToArray();

            //Timed Algorithms

            tests[2] = (prod) => mxp.GreedyTime(
                plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                plant.Depth * prod,
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(prod),
                transitions
                ).ToArray();

            tests[3] = (prod) => mxp.TimedMaximumParallelism(
                plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                plant.Depth * prod,
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(prod),
                transitions
                ).ToArray();
            
            tests[4] = (prod) => mxp.HeuristicShortestMakespan(
                plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                plant.Depth * prod,
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(prod),
                transitions
                ).ToArray();

            // GU-Comment: Funções de contagem de tempo e paralelismo 

            Func<int, AbstractEvent[], float> time = (prod, seq) => mxp.TimeEvaluation(
                plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                seq,
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(prod),
                transitions
                );

            Func<int, AbstractEvent[], float> paralell = (prod, seq) => mxp.ParallelismEvaluation(
                plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                seq,
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(prod),
                transitions
                );

            Console.WriteLine("Configurações terminadas\nSupervisor com {0} estados e {1} transições",
                plant.Supervisor.States.Count(),
                plant.Supervisor.Transitions.Count()
                );


            // GU-Comment: chama os testes e varia a quantidade  de produtos
            var count = 0;
            foreach (var test in tests)
            {
                Console.WriteLine("\n-------------------------------------\n");
                Console.WriteLine(" teste {0}\n", count = count + 1);

                foreach (var products in new[] { 7 })  // 1, 5, 10, 50, 100, 500, 1000 })
                {
                    var lst = new List<AbstractEvent[]>();

                    Stopwatch timer = new Stopwatch();
                    timer.Start();
                    for (var it = 0; it < maxIt; it++)
                        lst.Add(test(products));
                    timer.Stop();

                    var optimizationTime = timer.ElapsedMilliseconds / maxIt;

                    var makespan = lst.Select(
                        s => time(products, s))
                        .Average();

                    var parallelism = lst.Select(
                        s => paralell(products, s))
                        .Average();

                    Console.Write(
                        "{{{0},{1},{2},{3}}}, ",
                        products,
                        optimizationTime,
                        float.IsNaN(makespan) ? -1.0f : makespan,
                        parallelism
                        );
                }
            }
            //Console.ReadLine();
        }
    }
}
