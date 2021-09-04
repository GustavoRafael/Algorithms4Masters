using System;
using System.Collections;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Formatters.Binary;
using System.Threading.Tasks;
using UltraDES;
using Scheduler = System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>;
using Restriction = System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, uint>;
using Update = System.Func
    <System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>, UltraDES.AbstractEvent,
        System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>>;
using DFA = UltraDES.DeterministicFiniteAutomaton;
using TimeContext = System.Tuple
    <TestesMestrado.SinglyLinkedList<UltraDES.AbstractEvent>, System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>,
        System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, uint>, float>;

namespace TestesMestrado
{
    internal class Program
    {
        const int limiar = 1000000000;

        private static void Main()
        {
            System.Threading.Thread.CurrentThread.Priority = System.Threading.ThreadPriority.AboveNormal;

            float maxIt = 1;
            ISchedulingProblem plant = new SFM();

            var transitions = plant.Supervisor.Transitions.AsParallel()
                .GroupBy(t => t.Origin)
                .ToDictionary(gr => gr.Key, gr => gr.ToArray());

#if DEBUG

            var collisions = transitions.Keys.Select(k => k.GetHashCode()).GroupBy(h => h).Select(ge => ge.Count()).Max();
            Debug.WriteLine($"Max collisions on transitions: {collisions}");

#endif

            Func<int, AbstractEvent[]>[] tests = new Func<int, AbstractEvent[]>[5];

           //Logical Algorithms

            tests[1] = (prod) =>
               GreedyParallelism(plant.Supervisor, plant.InitialState, plant.TargetState, plant.Depth * prod,
                   plant.InitialScheduler, plant.UpdateFunction, plant.InitialRestrition(prod), transitions).ToArray();

            tests[0] = (prod) =>
                LogicalMaximumParallelism(plant.Supervisor, plant.InitialState, plant.Depth * prod, plant.TargetState,
                    plant.InitialRestrition(prod), transitions).ToArray();

            //Timed Algorithms

            tests[2] = (prod) =>
                GreedyTime(plant.Supervisor, plant.InitialState, plant.TargetState, plant.Depth * prod,
                    plant.InitialScheduler, plant.UpdateFunction, plant.InitialRestrition(prod), transitions).ToArray();

            tests[3] = (prod) =>
               TimedMaximumParallelism(plant.Supervisor, plant.InitialState, plant.TargetState, plant.Depth * prod,
                   plant.InitialScheduler, plant.UpdateFunction, plant.InitialRestrition(prod), transitions).ToArray();

            tests[4] = (prod) =>
               HeuristicShortestMakespan(plant.Supervisor, plant.InitialState, plant.TargetState, plant.Depth * prod,
                   plant.InitialScheduler, plant.UpdateFunction, plant.InitialRestrition(prod), transitions).ToArray();

            Func<int, AbstractEvent[], float> time =
                (prod, seq) => TimeEvaluation(plant.Supervisor, plant.InitialState, plant.TargetState, seq,
                    plant.InitialScheduler, plant.UpdateFunction, plant.InitialRestrition(prod), transitions);

            Func<int, AbstractEvent[], float> paralell =
                (prod, seq) => ParallelismEvaluation(plant.Supervisor, plant.InitialState, plant.TargetState, seq,
                    plant.InitialScheduler, plant.UpdateFunction, plant.InitialRestrition(prod), transitions);

            Console.WriteLine("Configurações terminadas\nSupervisor com {0} estados e {1} transições",
                plant.Supervisor.States.Count(), plant.Supervisor.Transitions.Count());

            foreach (var test in tests)
            {
                Console.WriteLine("\n-------------------------------------\n");

                foreach (var products in new[] { 1, 5, 10, 50, 100, 500, 1000 })
                {
                    var lst = new List<AbstractEvent[]>();
                    Stopwatch timer = new Stopwatch();
                    timer.Start();
                    for (var it = 0; it < maxIt; it++)
                        lst.Add(test(products));
                    timer.Stop();

                    var optimizationTime = timer.ElapsedMilliseconds / maxIt;
                    var makespan = lst.Select(s => time(products, s)).Average();
                    var parallelism = lst.Select(s => paralell(products, s)).Average();

                    Console.Write("{{{0},{1},{2},{3}}}, ", products, optimizationTime, float.IsNaN(makespan) ? -1.0f : makespan, parallelism);
                }
            }

            Console.ReadLine();
        }

        private static IEnumerable<AbstractEvent> GreedyTime(DFA S, AbstractState initial, AbstractState destination,
            int depth, Scheduler sch, Update update, Restriction res, Dictionary<AbstractState, Transition[]> transitions)
        {
            res = new Restriction(res);

            var state = initial;
            var events = new List<AbstractEvent>();

            for (var it = 0; it < depth; it++)
            {
                var trans =
                    transitions[state].Where(
                        t => (t.Trigger.IsControllable && res[t.Trigger] > 0) || !t.Trigger.IsControllable)
                        .OrderBy(t => sch[t.Trigger])
                        .First();

                state = trans.Destination;
                var e = trans.Trigger;

                events.Add(e);

                if (e.IsControllable) res[e]--;

                sch = update(sch, e);
            }

            return events.ToArray();
        }

        private static IEnumerable<AbstractEvent> GreedyParallelism(DFA S, AbstractState initial, AbstractState destination,
            int depth, Scheduler sch, Update update, Restriction res, Dictionary<AbstractState, Transition[]> transitions)
        {
            res = new Restriction(res);

            var state = initial;
            var events = new List<AbstractEvent>();

            for (var it = 0; it < depth; it++)
            {
                var translst = transitions[state].Where(t => (t.Trigger.IsControllable && res[t.Trigger] > 0)).ToList();

                var aux = transitions[state].Where(t => !t.IsControllableTransition)
                           .Select(t => t.Trigger)
                           .Distinct().ToArray();

                if (aux.Any())
                {
                    var min = aux.Min(ev => sch[ev]);
                    translst.AddRange(transitions[state].Where(t => !t.IsControllableTransition && sch[t.Trigger] == min));
                }

                var trans = translst
                    .OrderByDescending(t => (t.Destination as CompoundExpandedState).Tasks)
                    .First();

                state = trans.Destination;
                var e = trans.Trigger;

                events.Add(e);

                if (e.IsControllable) res[e]--;

                sch = update(sch, e);
            }

            return events.ToArray();
        }

        private static float TimeEvaluation(DFA S, AbstractState initial, AbstractState destination,
            AbstractEvent[] sequence, Scheduler sch, Update update, Restriction res, Dictionary<AbstractState, Transition[]> transitions)
        {
            res = new Restriction(res);

            var state = initial;
            var events = new List<AbstractEvent>();

            float time = 0;

            foreach (var e in sequence)
            {
                var trans =
                    transitions[state].Where(
                        t => (t.Trigger.IsControllable && res[t.Trigger] > 0) || !t.Trigger.IsControllable)
                        .Single(t => t.Trigger == e);

                state = trans.Destination;

                events.Add(e);

                if (e.IsControllable) res[e]--;
                time += sch[e];
                sch = update(sch, e);
            }

            return state == destination ? time : float.PositiveInfinity;
        }

        private static float ParallelismEvaluation(DFA S, AbstractState initial, AbstractState destination,
            AbstractEvent[] sequence, Scheduler sch, Update update, Restriction res, Dictionary<AbstractState, Transition[]> transitions)
        {
            res = new Restriction(res);

            var state = initial;
            var events = new List<AbstractEvent>();

            float time = 0;
            float parallelism = 0;

            foreach (var e in sequence)
            {
                var trans = transitions[state].Where(t => (t.Trigger.IsControllable && res[t.Trigger] > 0) || !t.Trigger.IsControllable)
                        .Single(t => t.Trigger == e);

                state = trans.Destination;
                var w = (state as CompoundExpandedState).Tasks;
                
                parallelism += w;

                events.Add(e);

                Debug.WriteLine("{{{0}, {1}}}, ", e, w);

                if (e.IsControllable) res[e]--;
                time += sch[e];
                sch = update(sch, e);
            }

            return state == destination ? parallelism : float.PositiveInfinity;
        }

        private static IEnumerable<AbstractEvent> HeuristicShortestMakespan(DFA g, AbstractState initial,
            AbstractState target, int depth, Scheduler sch, Update update, Restriction res, Dictionary<AbstractState, Transition[]> transitions)
        {
            var distance = new Dictionary<AbstractState, List<Tuple<SinglyLinkedList<AbstractEvent>, Scheduler, Restriction, float>>>();

            distance.Add(initial, new List<TimeContext> {Tuple.Create(SinglyLinkedList<AbstractEvent>.Empty, sch, res, 0f)});

            for (var it = 0; it < depth; it++)
            {
                var distance2 = new Dictionary<AbstractState, List<TimeContext>>(distance.Count);

                Action<KeyValuePair<AbstractState, List<TimeContext>>> f = kvp =>
                {
                    var s = kvp.Key;
                    foreach (var context in kvp.Value)
                    {
                        var events = context.Item1;
                        var schA = context.Item2;
                        var resA = context.Item3;
                        var time = context.Item4;

                        var trans =
                            transitions[s].Where(t => t.IsControllableTransition && resA[t.Trigger] > 0 &&
                                    !update(schA, t.Trigger).Any(k => float.IsNaN(k.Value))).ToList();

                        if (trans.Count == 0)
                        {
                            var min =
                                transitions[s].Where(t => !t.IsControllableTransition)
                                    .Select(t => t.Trigger)
                                    .Distinct()
                                    .Min(e => schA[e]);
                            trans.AddRange(
                                transitions[s].Where(t => !t.IsControllableTransition && schA[t.Trigger] == min));
                        }

                        foreach (var tran in trans)
                        {
                            var e = tran.Trigger;
                            var sB = tran.Destination;

                            var eventsB = events.Prepend(e);

                            var resB = new Restriction(resA);
                            if (e.IsControllable) resB[e]--;

                            var schB = update(schA, e);

                            time += schA[e];

                            lock (distance2)
                            {
                                if (!distance2.ContainsKey(sB))
                                    distance2.Add(sB, new List<TimeContext> {Tuple.Create(eventsB, schB, resB, time)});
                                else
                                {
                                    var actual = distance2[sB].Where(tc => tc.Item2.All(k => k.Value == schB[k.Key]));
                                    if (actual.Any())
                                    {
                                        var tc = actual.Single();

                                        if (!(tc.Item4 > time)) continue;
                                        distance2[sB].Remove(tc);
                                        distance2[sB].Add(Tuple.Create(eventsB, schB, resB, time));
                                    }
                                    else
                                    {
                                        distance2[sB].Add(Tuple.Create(eventsB, schB, resB, time));
                                    }
                                }
                            }
                        }
                    }
                };

                //GCSettings.LatencyMode = GCLatencyMode.LowLatency;
                if (distance.Count > limiar) Parallel.ForEach(distance, f);
                else foreach (var kvp in distance) f(kvp);
                //GCSettings.LatencyMode = GCLatencyMode.Batch;

                distance = distance2;
            }

            return distance[target].OrderBy(c => c.Item4).First().Item1.Reverse().ToArray();
        }

        private static IEnumerable<AbstractEvent> LogicalMaximumParallelism(DFA g, AbstractState initial, int depth,
            AbstractState target, Restriction res, Dictionary<AbstractState, Transition[]> transitions)
        {
            if (initial == null) initial = target;
            int max = g.States.Count();

            IDictionary<AbstractState, Tuple<uint, SinglyLinkedList<AbstractEvent>, Restriction>> distance = new Dictionary<AbstractState, Tuple<uint, SinglyLinkedList<AbstractEvent>, Restriction>>
            {
                { initial, Tuple.Create(0u, SinglyLinkedList<AbstractEvent>.Empty, res) }
            };

            for (var i = 0; i < depth; i++)
            {
#if DEBUG
                var collisions = distance.Keys.Select(k => k.GetHashCode()).GroupBy(h => h).Select(ge => ge.Count()).Max();
                if(collisions > 1) Debug.WriteLine($"Max collisions {collisions}");
                Debug.WriteLine($"Dictionary Size: {max} | Used Size: {distance.Count}");
#endif

                max = (int)(distance.Count * 1.1);

                long size = 1024*1024*100;

                if (distance.Count > limiar)
                {
                    var nextDistance = new ConcurrentDictionary<AbstractState, Tuple<uint, SinglyLinkedList<AbstractEvent>, Restriction>>(Environment.ProcessorCount, max);
                    var par = Partitioner.Create(distance);

                    //bool gc = GC.TryStartNoGCRegion(size);

                    Parallel.ForEach(par, kvp =>
                    {
                        var s1 = kvp.Key;
                        var d = kvp.Value;
                        var res1 = d.Item3;
                        var events = d.Item2;

                        var trans = transitions[s1].Where(t => t.IsControllableTransition && res1[t.Trigger] > 0).ToList();

                        if (!trans.Any()) trans.AddRange(transitions[s1].Where(t => !t.IsControllableTransition));

                        foreach (var t in trans)
                        {
                            var s2 = t.Destination;
                            var e = t.Trigger;

                            var w = d.Item1;
                            w += ((CompoundExpandedState)s2).Tasks;

                            var eventsB = events.Prepend(e);

                            var res2 = e.IsControllable ? new Restriction(res1) : res1;
                            if (e.IsControllable) res2[e]--;

                            nextDistance.AddOrUpdate(s2, Tuple.Create(w, eventsB, res2),
                                (k, v) => v.Item1 < w ? Tuple.Create(w, eventsB, res2) : v);
                        }
                    });

                    //if (gc) GC.EndNoGCRegion();

                    distance = nextDistance;

                 
                }
                else
                {
                    var nextDistance = new Dictionary<AbstractState, Tuple<uint, SinglyLinkedList<AbstractEvent>, Restriction>>(max);

                    //bool gc = GC.TryStartNoGCRegion(size);

                    foreach (var kvp in distance)
                    {
                        var s1 = kvp.Key;
                        var d = kvp.Value;
                        var res1 = d.Item3;
                        var events = d.Item2;

                        var trans = transitions[s1].Where(t => t.IsControllableTransition && res1[t.Trigger] > 0).ToList();

                        if (!trans.Any()) trans.AddRange(transitions[s1].Where(t => !t.IsControllableTransition));

                        foreach (var t in trans)
                        {
                            var s2 = t.Destination;
                            var e = t.Trigger;

                            var w = d.Item1;
                            w += ((CompoundExpandedState)s2).Tasks;

                            var eventsB = events.Prepend(e);

                            var res2 = e.IsControllable ? new Restriction(res1) : res1;
                            if (e.IsControllable) res2[e]--;

                            if (nextDistance.ContainsKey(s2))
                            {
                                if (nextDistance[s2].Item1 < w)
                                    nextDistance[s2] = Tuple.Create(w, eventsB, res2);
                            }
                            else
                                nextDistance.Add(s2, Tuple.Create(w, eventsB, res2));

                        }
                    }

                   //if (gc) GC.EndNoGCRegion();

                    distance = nextDistance;

                    
                }            

            }
            if (!distance.ContainsKey(target)) return null;
            var lst = distance[target].Item2.ToList();
            lst.Reverse();
            return lst;
        }

        private static IEnumerable<AbstractEvent> TimedMaximumParallelism(DFA g, AbstractState initial,
            AbstractState target, int depth, Scheduler sch, Update update, Restriction res, Dictionary<AbstractState, Transition[]> transitions)
        {
            if (initial == null) initial = target;

            IDictionary<AbstractState, TimeContext> distance = new Dictionary<AbstractState, TimeContext>();
            distance.Add(initial, Tuple.Create(SinglyLinkedList<AbstractEvent>.Empty, sch, res, 0f));

            for (var i = 0; i < depth; i++)
            {
                if (distance.Count > limiar)
                {
                    var nextDistance = new ConcurrentDictionary<AbstractState, TimeContext>(Environment.ProcessorCount, distance.Count);
                    Parallel.ForEach(Partitioner.Create(distance), kvp =>
                    {
                        var s = kvp.Key;
                        var d = kvp.Value;
                        var resA = d.Item3;
                        var schA = d.Item2;
                        var events = d.Item1;

                        var trans =
                            transitions[s].Where(t => t.IsControllableTransition && resA[t.Trigger] > 0 &&
                                    !update(schA, t.Trigger).Any(k => float.IsNaN(k.Value))).ToList();

                        var aux = transitions[s].Where(t => !t.IsControllableTransition)
                            .Select(t => t.Trigger)
                            .Distinct().ToArray();

                        if (aux.Any() && !trans.Any())
                        {
                            var min = aux.Min(e => schA[e]);
                            trans.AddRange(
                                transitions[s].Where(t => !t.IsControllableTransition && schA[t.Trigger] == min));
                        }

                        foreach (var t in trans)
                        {
                            var s2 = t.Destination;
                            var e = t.Trigger;

                            var w = d.Item4;
                            if (s2 is CompoundExpandedState) w += ((CompoundExpandedState)s2).Tasks;
                            else if (s2 is ExpandedState) w += ((ExpandedState)s2).Tasks;

                            var eventsB = events.Prepend(e);

                            var res2 = e.IsControllable ? new Restriction(resA) : resA;
                            if (e.IsControllable) res2[e]--;

                            var schB = update(schA, e);

                            nextDistance.AddOrUpdate(s2, Tuple.Create(eventsB, schB, res2, w),
                                (k, v) => v.Item4 < w ? Tuple.Create(eventsB, schB, res2, w) : v);
                        }
                    });
                    distance = nextDistance;
                }
                else
                {
                    var nextDistance = new Dictionary<AbstractState, TimeContext>(distance.Count);
                    foreach (var kvp in distance)
                    {
                        var s = kvp.Key;
                        var d = kvp.Value;
                        var resA = d.Item3;
                        var schA = d.Item2;
                        var events = d.Item1;

                        var trans =
                            transitions[s].Where(
                                t =>
                                    t.IsControllableTransition && resA[t.Trigger] > 0 &&
                                    !update(schA, t.Trigger).Any(k => float.IsNaN(k.Value))).ToList();

                        var aux = transitions[s].Where(t => !t.IsControllableTransition)
                            .Select(t => t.Trigger)
                            .Distinct().ToArray();

                        if (aux.Any() && !trans.Any())
                        {
                            var min = aux.Min(e => schA[e]);
                            trans.AddRange(
                                transitions[s].Where(t => !t.IsControllableTransition && schA[t.Trigger] == min));
                        }

                        foreach (var t in trans)
                        {
                            var s2 = t.Destination;
                            var e = t.Trigger;

                            var w = d.Item4;
                            if (s2 is CompoundExpandedState) w += ((CompoundExpandedState)s2).Tasks;
                            else if (s2 is ExpandedState) w += ((ExpandedState) s2).Tasks;

                            var eventsB = events.Prepend(e);

                            var res2 = e.IsControllable ? new Restriction(resA) : resA;
                            if (e.IsControllable) res2[e]--;

                            var schB = update(schA, e);

                            if(schB.Any(k => float.IsNaN(k.Value))) continue;


                            if (nextDistance.ContainsKey(s2))
                            {
                                if (nextDistance[s2].Item4 < w)
                                    nextDistance[s2] = Tuple.Create(eventsB, schB, res2, w);
                            }
                            else
                                nextDistance.Add(s2, Tuple.Create(eventsB, schB, res2, w));

                        }
                    }
                    distance = nextDistance;
                }
            }


            //GCSettings.LatencyMode = GCLatencyMode.Batch;
            return !distance.ContainsKey(target) ? null : distance[target].Item1.Reverse().ToArray();
        }
    }

    internal class SFM : ISchedulingProblem
    {
        private readonly Dictionary<int, Event> _e;

        public SFM()
        {
           _e = new[]
            {
                11, 12, 21, 22, 41,
                42, 51, 52, 53, 54, 31,
                32, 33, 34, 35, 36, 37, 38, 39, 30, 61,
                63, 65, 64, 66, 71, 72, 73, 74, 81, 82
            }.ToDictionary(alias => alias,
                alias =>
                    new Event(alias.ToString(),
                        alias%2 == 0 ? Controllability.Uncontrollable : Controllability.Controllable));

            if (File.Exists("SFM.bin"))
            {
                Supervisor = Utilidades.DeserializeAutomaton("SFM.bin");
            }
            else
            {

                var s = Enumerable.Range(0, 6)
               .ToDictionary(i => i,
                   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

                // C1

                var c1 = new DFA(
                    new[]
                    {
                        new Transition(s[0], _e[11], s[1]),
                        new Transition(s[1], _e[12], s[0])
                    },
                    s[0], "C1");

                // C2

                var c2 = new DFA(
                    new[]
                    {
                        new Transition(s[0], _e[21], s[1]),
                        new Transition(s[1], _e[22], s[0])
                    },
                    s[0], "C2");

                // Fresa

                var fresa = new DFA(
                    new[]
                    {
                        new Transition(s[0], _e[41], s[1]),
                        new Transition(s[1], _e[42], s[0])
                    },
                    s[0], "Fresa");

                // MP

                var mp = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[81], s[1]),
                        new Transition(s[1], _e[82], s[0])
                    },
                    s[0], "MP");

                // Torno

                var torno = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[51], s[1]),
                        new Transition(s[1], _e[52], s[0]),
                        new Transition(s[0], _e[53], s[2]),
                        new Transition(s[2], _e[54], s[0])
                    },
                    s[0], "Torno");

                // C3

                var c3 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[71], s[1]),
                        new Transition(s[1], _e[72], s[0]),
                        new Transition(s[0], _e[73], s[2]),
                        new Transition(s[2], _e[74], s[0])
                    },
                    s[0], "C3");

                // Robô

                var robot = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[31], s[1]),
                        new Transition(s[1], _e[32], s[0]),
                        new Transition(s[0], _e[33], s[2]),
                        new Transition(s[2], _e[34], s[0]),
                        new Transition(s[0], _e[35], s[3]),
                        new Transition(s[3], _e[36], s[0]),
                        new Transition(s[0], _e[37], s[4]),
                        new Transition(s[4], _e[38], s[0]),
                        new Transition(s[0], _e[39], s[5]),
                        new Transition(s[5], _e[30], s[0])
                    },
                    s[0], "Robot");

                // MM

                var mm = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[61], s[1]),
                        new Transition(s[1], _e[63], s[2]),
                        new Transition(s[1], _e[65], s[3]),
                        new Transition(s[2], _e[64], s[0]),
                        new Transition(s[3], _e[66], s[0])
                    },
                    s[0], "MM");

                // Especificações

                s = Enumerable.Range(0, 6)
                    .ToDictionary(i => i,
                        i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

                // E1

                var e1 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[12], s[1]),
                        new Transition(s[1], _e[31], s[0])
                    },
                    s[0], "E1");

                // E2

                var e2 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[22], s[1]),
                        new Transition(s[1], _e[33], s[0])
                    },
                    s[0], "E2");

                // E5

                var e5 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[36], s[1]),
                        new Transition(s[1], _e[61], s[0])
                    },
                    s[0], "E5");

                // E6

                var e6 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[38], s[1]),
                        new Transition(s[1], _e[63], s[0])
                    },
                    s[0], "E6");

                // E3

                var e3 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[32], s[1]),
                        new Transition(s[1], _e[41], s[0]),
                        new Transition(s[0], _e[42], s[2]),
                        new Transition(s[2], _e[35], s[0])
                    },
                    s[0], "E3");

                // E7

                var e7 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[30], s[1]),
                        new Transition(s[1], _e[71], s[0]),
                        new Transition(s[0], _e[74], s[2]),
                        new Transition(s[2], _e[65], s[0])
                    },
                    s[0], "E7");

                // E8

                var e8 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[72], s[1]),
                        new Transition(s[1], _e[81], s[0]),
                        new Transition(s[0], _e[82], s[2]),
                        new Transition(s[2], _e[73], s[0])
                    },
                    s[0], "E8");

                // E4

                var e4 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[34], s[1]),
                        new Transition(s[1], _e[51], s[0]),
                        new Transition(s[1], _e[53], s[0]),
                        new Transition(s[0], _e[52], s[2]),
                        new Transition(s[2], _e[37], s[0]),
                        new Transition(s[0], _e[54], s[3]),
                        new Transition(s[3], _e[39], s[0])
                    },
                    s[0], "E4");

                Supervisor = DFA.MonoliticSupervisor(new[] {c1, c2, fresa, torno, robot, mm, c3, mp},
                    new[] {e1, e2, e3, e4, e5, e6, e7, e8}, true);

                Utilidades.SerializeAutomaton(Supervisor, "SFM.bin");
            }
        }

        public DFA Supervisor { get; }

        public int Depth => 44;

        public AbstractState InitialState => Supervisor.InitialState;

        public AbstractState TargetState => Supervisor.InitialState;

        public Restriction InitialRestrition(int products)
        {
            return new Restriction
            {
                {_e[11], (uint) (2*products)},
                {_e[21], (uint) (2*products)},
                {_e[31], (uint) (2*products)},
                {_e[33], (uint) (2*products)},
                {_e[35], (uint) (2*products)},
                {_e[37], (uint) (1*products)},
                {_e[39], (uint) (1*products)},
                {_e[41], (uint) (2*products)},
                {_e[51], (uint) (1*products)},
                {_e[53], (uint) (1*products)},
                {_e[61], (uint) (2*products)},
                {_e[63], (uint) (1*products)},
                {_e[65], (uint) (1*products)},
                {_e[71], (uint) (1*products)},
                {_e[73], (uint) (1*products)},
                {_e[81], (uint) (1*products)}
            };
        }

        public Scheduler InitialScheduler =>
                _e.ToDictionary(kvp => kvp.Value as AbstractEvent,
                    kvp => kvp.Value.IsControllable ? 0.0f : float.PositiveInfinity);

        public Update UpdateFunction => (old, ev) =>
        {
            var sch = old.ToDictionary(kvp => kvp.Key, kvp =>
            {
                var v = kvp.Value - old[ev];

                if (kvp.Key.IsControllable) return v < 0 ? 0 : v;
                if (v < 0) return float.NaN;
                return v;
            });

            if (!ev.IsControllable) sch[ev] = float.PositiveInfinity;

            switch (ev.ToString())
            {
                case "11":
                    sch[_e[12]] = 25;
                    break;
                case "21":
                    sch[_e[22]] = 25;
                    break;
                case "31":
                    sch[_e[32]] = 21;
                    break;
                case "33":
                    sch[_e[34]] = 19;
                    break;
                case "35":
                    sch[_e[36]] = 16;
                    break;
                case "37":
                    sch[_e[38]] = 24;
                    break;
                case "39":
                    sch[_e[30]] = 20;
                    break;
                case "41":
                    sch[_e[42]] = 30;
                    break;
                case "51":
                    sch[_e[52]] = 38;
                    break;
                case "53":
                    sch[_e[54]] = 32;
                    break;
                case "61":
                    sch[_e[63]] = 15;
                    sch[_e[65]] = 15;
                    break;
                case "63":
                    sch[_e[64]] = 25;
                    break;
                case "65":
                    sch[_e[66]] = 25;
                    break;
                case "71":
                    sch[_e[72]] = 25;
                    break;
                case "73":
                    sch[_e[74]] = 25;
                    break;
                case "81":
                    sch[_e[82]] = 24;
                    break;
            }
            return sch;
        };
    }

    internal class SF : ISchedulingProblem
    {
        private readonly Dictionary<int, Event> _e;

        public SF()
        {
            var s = new[] {new ExpandedState("0", 0, Marking.Marked), new ExpandedState("1", 1, Marking.Unmarked)};

            _e = new[] {1, 2, 3, 4}.ToDictionary(alias => alias, alias =>
                new Event(alias.ToString(),
                    alias%2 == 0 ? Controllability.Uncontrollable : Controllability.Controllable));

            var m1 = new DeterministicFiniteAutomaton(
                new[]
                {
                    new Transition(s[0], _e[1], s[1]),
                    new Transition(s[1], _e[2], s[0])
                },
                s[0], "M1");

            var m2 = new DeterministicFiniteAutomaton(
                new[]
                {
                    new Transition(s[0], _e[3], s[1]),
                    new Transition(s[1], _e[4], s[0])
                },
                s[0], "M2");

            s = new[] {new ExpandedState("E", 0, Marking.Marked), new ExpandedState("F", 0, Marking.Unmarked)};

            var e1 = new DeterministicFiniteAutomaton(
                new[]
                {
                    new Transition(s[0], _e[2], s[1]),
                    new Transition(s[1], _e[3], s[0])
                },
                s[0], "E");

            Supervisor = DFA.MonoliticSupervisor(new[] {m1, m2},
                new[] {e1}, true);
        }

        public int Depth => 4;

        public Scheduler InitialScheduler =>
            _e.ToDictionary(kvp => kvp.Value as AbstractEvent,
                kvp => kvp.Value.IsControllable ? 0.0f : float.PositiveInfinity);

        public AbstractState InitialState => Supervisor.InitialState;

        public DFA Supervisor { get; }

        public AbstractState TargetState => Supervisor.InitialState;

        public Update UpdateFunction => (old, ev) =>
        {
            var sch = old.ToDictionary(kvp => kvp.Key, kvp =>
            {
                if (kvp.Key.IsControllable) return 0;

                var v = kvp.Value - old[ev];

                return v < 0 ? float.PositiveInfinity : v;
            });

            if (!ev.IsControllable) sch[ev] = float.PositiveInfinity;

            switch (ev.ToString())
            {
                case "1":
                    sch[_e[2]] = 25 + 1;
                    break;
                case "3":
                    sch[_e[4]] = 25 + 1;
                    break;
            }
            return sch;
        };

        public Restriction InitialRestrition(int products)
        {
            return new Restriction
            {
                {_e[1], (uint) (1*products)},
                {_e[3], (uint) (1*products)}
            };
        }
    }

    internal class ITL : ISchedulingProblem
    {
        private readonly Dictionary<int, Event> _e;

        public ITL()
        {
            _e = new[] { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 }.ToDictionary(alias => alias, alias =>
                 new Event(alias.ToString(),
                     alias % 2 == 0 ? Controllability.Uncontrollable : Controllability.Controllable));

            if (File.Exists("ITL.bin"))
            {
                Supervisor = Utilidades.DeserializeAutomaton("ITL.bin");
            }
            else
            {

                var s = new[] {new ExpandedState("0", 0, Marking.Marked), new ExpandedState("1", 1, Marking.Unmarked)};



                var m1 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[1], s[1]),
                        new Transition(s[1], _e[2], s[0])
                    },
                    s[0], "M1");

                var m2 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[3], s[1]),
                        new Transition(s[1], _e[4], s[0])
                    },
                    s[0], "M2");

                var m3 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[5], s[1]),
                        new Transition(s[1], _e[6], s[0])
                    },
                    s[0], "M3");

                var m4 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[7], s[1]),
                        new Transition(s[1], _e[8], s[0])
                    },
                    s[0], "M4");

                var m5 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[9], s[1]),
                        new Transition(s[1], _e[10], s[0])
                    },
                    s[0], "M5");

                var m6 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[11], s[1]),
                        new Transition(s[1], _e[12], s[0])
                    },
                    s[0], "M6");

                s = Enumerable.Range(0, 4)
                    .Select(i =>
                        new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked))
                    .ToArray();

                var e1 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[2], s[1]),
                        new Transition(s[1], _e[3], s[0])
                    },
                    s[0], "E1");

                var e2 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[6], s[1]),
                        new Transition(s[1], _e[7], s[0])
                    },
                    s[0], "E2");

                var e3 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[4], s[1]),
                        new Transition(s[1], _e[8], s[2]),
                        new Transition(s[0], _e[8], s[3]),
                        new Transition(s[3], _e[4], s[2]),
                        new Transition(s[2], _e[9], s[0])
                    },
                    s[0], "E3");

                var e4 = new DeterministicFiniteAutomaton(
                    new[]
                    {
                        new Transition(s[0], _e[10], s[1]),
                        new Transition(s[1], _e[11], s[0])
                    },
                    s[0], "E4");

                Supervisor = DFA.MonoliticSupervisor(new[] {m1, m2, m3, m4, m5, m6},
                    new[] {e1, e2, e3, e4}, true);

                Utilidades.SerializeAutomaton(Supervisor, "ITL.bin");
            }
        }

        public int Depth => 12;

        public Scheduler InitialScheduler =>
            _e.ToDictionary(kvp => kvp.Value as AbstractEvent,
                kvp => kvp.Value.IsControllable ? 0.0f : float.PositiveInfinity);

        public AbstractState InitialState => Supervisor.InitialState;

        public DFA Supervisor { get; }

        public AbstractState TargetState => Supervisor.InitialState;

        public Update UpdateFunction => (old, ev) =>
        {
            var sch = old.ToDictionary(kvp => kvp.Key, kvp =>
            {
                var v = kvp.Value - old[ev];

                if (kvp.Key.IsControllable) return v < 0 ? 0 : v;
                return v < 0 ? float.NaN : v;
            });

            if (!ev.IsControllable) sch[ev] = float.PositiveInfinity;

            if (ev == _e[1]) sch[_e[2]] = 25;
            if (ev == _e[3]) sch[_e[4]] = 25;
            if (ev == _e[5]) sch[_e[6]] = 38;
            if (ev == _e[7]) sch[_e[8]] = 21;
            if (ev == _e[9]) sch[_e[10]] = 19;
            if (ev == _e[11]) sch[_e[12]] = 24;

            return sch;
        };

        public Restriction InitialRestrition(int products)
        {
            return new Restriction
            {
                {_e[01], (uint) (1*products)},
                {_e[03], (uint) (1*products)},
                {_e[05], (uint) (1*products)},
                {_e[07], (uint) (1*products)},
                {_e[09], (uint) (1*products)},
                {_e[11], (uint) (1*products)},
            };
        }
    }

    internal static class Utilidades
    {
        public static void SerializeAutomaton(DeterministicFiniteAutomaton G, string path)
        {
            IFormatter formatter = new BinaryFormatter();
            Stream stream = new FileStream(path, FileMode.Create, FileAccess.Write, FileShare.None);
            formatter.Serialize(stream, G);
            stream.Close();
        }

        public static DFA DeserializeAutomaton(string path)
        {
            IFormatter formatter = new BinaryFormatter();
            Stream stream = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.Read);
            var obj = formatter.Deserialize(stream) as DFA;
            stream.Close();
            return obj;
        }
    }

    public sealed class SinglyLinkedList<T> : IEnumerable<T>
    {
        readonly T _head;
        readonly SinglyLinkedList<T> _tail;

        private SinglyLinkedList()
        {
            IsEmpty = true;
        }

        private SinglyLinkedList(T head)
        {
            IsEmpty = false;
            _head = head;
        }

        private SinglyLinkedList(T head, SinglyLinkedList<T> tail)
        {
            IsEmpty = false;
            _head = head;
            _tail = tail;
        }

        public static SinglyLinkedList<T> Empty { get; } = new SinglyLinkedList<T>();

        public int Count
        {
            get
            {
                var list = this;
                var count = 0;
                while (!list.IsEmpty)
                {
                    count++;
                    list = list._tail;
                }
                return count;
            }
        }

        public bool IsEmpty { get; }

        public T Head
        {
            get
            {
                if (IsEmpty)
                    throw new InvalidOperationException("The list is empty.");
                return _head;
            }
        }

        public SinglyLinkedList<T> Tail
        {
            get
            {
                if (_tail == null)
                    throw new InvalidOperationException("This list has no tail.");
                return _tail;
            }
        }

        public static SinglyLinkedList<T> FromEnumerable(IEnumerable<T> e)
        {
            if (e == null)
                throw new ArgumentNullException(nameof(e));
            return FromArrayInternal(e.ToArray());
        }

        public static SinglyLinkedList<T> FromArray(params T[] a)
        {
            if (a == null)
                throw new ArgumentNullException(nameof(a));
            return FromArrayInternal(a);
        }

        public SinglyLinkedList<T> Append(T value)
        {
            var array = new T[Count + 1];
            var list = this;
            var index = 0;
            while (!list.IsEmpty)
            {
                array[index++] = list._head;
                list = list._tail;
            }
            array[index] = value;
            return FromArrayInternal(array);
        }

        public SinglyLinkedList<T> Prepend(T value)
        {
            return new SinglyLinkedList<T>(value, this);
        }

        public SinglyLinkedList<T> Insert(int index, T value)
        {
            if (index < 0)
                throw new ArgumentOutOfRangeException(nameof(index), "Cannot be less than zero.");
            var count = Count;
            if (index >= count)
                throw new ArgumentOutOfRangeException(nameof(index), "Cannot be greater than count.");
            var array = new T[Count + 1];
            var list = this;
            var arrayIndex = 0;
            while (!list.IsEmpty)
            {
                if (arrayIndex == index)
                {
                    array[arrayIndex++] = value;
                }
                array[arrayIndex++] = list._head;
                list = list._tail;
            }
            return FromArrayInternal(array);
        }

        public IEnumerator<T> GetEnumerator()
        {
            var list = this;
            while (!list.IsEmpty)
            {
                yield return list._head;
                list = list._tail;
            }
        }

        public override string ToString()
        {
            return IsEmpty ? "[]" : $"[{_head}...]";
        }

        IEnumerator IEnumerable.GetEnumerator()
        {
            return GetEnumerator();
        }

        private static SinglyLinkedList<T> FromArrayInternal(IReadOnlyList<T> a)
        {
            var result = Empty;
            for (var i = a.Count - 1; i >= 0; i--)
            {
                result = result.Prepend(a[i]);
            }
            return result;
        }
    }
}