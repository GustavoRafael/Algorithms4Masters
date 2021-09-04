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
    class ClassMXP
    {
        const int limiar = 100;

        public IEnumerable<AbstractEvent> GreedyTime(
           DFA S,
           AbstractState initial,
           AbstractState destination,
           int depth,
           Scheduler sch,
           Update update,
           Restriction res,
           Dictionary<AbstractState, Transition[]> transitions
           )
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


        public IEnumerable<AbstractEvent> GreedyParallelism(
            DFA S,
            AbstractState initial,
            AbstractState destination,
            int depth,
            Scheduler sch,
            Update update,
            Restriction res,
            Dictionary<AbstractState, Transition[]> transitions
            )
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
                    .OrderByDescending(t => t.Destination.ActiveTasks())
                    .First();

                state = trans.Destination;
                var e = trans.Trigger;

                events.Add(e);

                if (e.IsControllable) res[e]--;

                sch = update(sch, e);
            }

            return events.ToArray();
        }

        // GU- Comment: avalia o tempo da sequencia 
        public float TimeEvaluation(
            DFA S,
            AbstractState initial,
            AbstractState destination,
            AbstractEvent[] sequence,
            Scheduler sch,
            Update update,
            Restriction res,
            Dictionary<AbstractState, Transition[]> transitions
            )
        {
            res = new Restriction(res);

            var state = initial;
            var events = new List<AbstractEvent>();

            float time = 0;


            for (int i = 0; i <= sequence.Length; i++)
            {
                // teste se já chegou ao final da sequencia e todos os eventos são controláveis (kvalue == 0) ev_nc (kvalue== positive infinite)
                if (i == sequence.Length && sch.All(
                    kvp => (kvp.Key.IsControllable) ? kvp.Value == 0 :
                    float.IsPositiveInfinity(kvp.Value)))
                    break;

                var e = (i == sequence.Length) ? null : sequence[i];

                var trans = transitions[state].Where(
                    t => (t.Trigger.IsControllable && res[t.Trigger] > 0) || !t.Trigger.IsControllable);

                // trata os eventos factiveis- se tiver algum evento factivel
                if (trans.Any(t => t.Trigger == e))
                {
                    state = trans.Single(t => t.Trigger == e).Destination;

                    events.Add(e);

                    if (e.IsControllable) res[e]--;  // res[e] --  reduz a quantidade eventos relativa ao numero de produtos. 2 produtos = (e[1], e[1]), (e[3],e[3])
                    time += sch[e];
                    sch = update(sch, e);
                }
                else // trata quando não há eventos 
                {
                    var min = sch.Where(
                        kvp => !kvp.Key.IsControllable && transitions[state].Select(t => t.Trigger)
                        .Contains(kvp.Key))
                        .OrderBy(kvp => kvp.Value)
                        .First();

                    e = min.Key;

                    state = trans.Single(t => t.Trigger == e).Destination;

                    events.Add(e);
                    time += sch[e];
                    sch = update(sch, e);

                    i--;
                }


            }

            return state == destination ? time : float.PositiveInfinity;
        }


        // GU- Comment: não foi usada ate o ponto que eu chequei
        public float TimeEvaluationControllable(
            DFA S,
            AbstractState initial,
            AbstractState destination,
            AbstractEvent[] sequence,
            Scheduler sch,
            Update update,
            Restriction res,
            Dictionary<AbstractState, Transition[]> transitions
            )
        {
            res = new Restriction(res);

            var state = initial;
            var events = new List<AbstractEvent>();

            float time = 0;

            foreach (var e in sequence)
            {
                var trans = transitions[state].Where(t => (t.Trigger.IsControllable && res[t.Trigger] > 0))
                        .Single(t => t.Trigger == e);

                state = trans.Destination;

                events.Add(e);

                if (e.IsControllable) res[e]--;
                time += sch[e];
                sch = update(sch, e);
            }

            return state == destination ? time : float.PositiveInfinity;
        }


        public float ParallelismEvaluation(
            DFA S,
            AbstractState initial,
            AbstractState destination,
            AbstractEvent[] sequence,
            Scheduler sch,
            Update update,
            Restriction res,
            Dictionary<AbstractState, Transition[]> transitions
            )
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
                var w = state.ActiveTasks();

                parallelism += w;

                events.Add(e);

                //Debug.WriteLine("{{{0}, {1}}}, ", e, w);

                if (e.IsControllable) res[e]--;
                time += sch[e];
                sch = update(sch, e);
            }

            return state == destination ? parallelism : float.PositiveInfinity;
        }


        public IEnumerable<AbstractEvent> HeuristicShortestMakespan(
            DFA g,
            AbstractState initial,
            AbstractState target,
            int depth,
            Scheduler sch,
            Update update,
            Restriction res,
            Dictionary<AbstractState, Transition[]> transitions
            )
        {
            var distance = new Dictionary<AbstractState,
                List<Tuple<SinglyLinkedList<AbstractEvent>,
                Scheduler,
                Restriction,
                float>>>();

            distance.Add(
                initial,
                new List<TimeContext> {
                Tuple.Create(SinglyLinkedList<AbstractEvent>.Empty,
                sch,
                res,
                0f)
            });

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
                                    distance2.Add(sB, new List<TimeContext> { Tuple.Create(eventsB, schB, resB, time) });
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


        public IEnumerable<AbstractEvent> LogicalMaximumParallelism(
            DFA g,
            AbstractState initial,
            int depth,
            AbstractState target,
            Restriction res,
            Dictionary<AbstractState, Transition[]> transitions
            )
        {
            if (initial == null) initial = target;
            int max = g.States.Count();

            IDictionary<AbstractState, Tuple<uint, SinglyLinkedList<AbstractEvent>, Restriction>>
                distance = new Dictionary<AbstractState,
                Tuple<uint, SinglyLinkedList<AbstractEvent>,
                Restriction>>
            {
                { initial, Tuple.Create(0u, SinglyLinkedList<AbstractEvent>.Empty, res) }
            };

            for (var i = 0; i < depth; i++)
            {
#if DEBUG
                var collisions = distance.Keys.Select(k => k.GetHashCode()).GroupBy(h => h).Select(ge => ge.Count()).Max();
                if (collisions > 1) Debug.WriteLine($"Max collisions {collisions}");
                // Debug.WriteLine($"Dictionary Size: {max} | Used Size: {distance.Count}");
#endif

                max = (int)(distance.Count * 1.1);



                if (distance.Count > limiar)
                {
                    var nextDistance = new ConcurrentDictionary<AbstractState, Tuple<uint, SinglyLinkedList<AbstractEvent>, Restriction>>(Environment.ProcessorCount, max);
                    var par = Partitioner.Create(distance);

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
                            w += s2.ActiveTasks();

                            var eventsB = events.Prepend(e);

                            var res2 = e.IsControllable ? new Restriction(res1) : res1;
                            if (e.IsControllable) res2[e]--;

                            nextDistance.AddOrUpdate(s2, Tuple.Create(w, eventsB, res2),
                                (k, v) => v.Item1 < w ? Tuple.Create(w, eventsB, res2) : v);
                        }
                    });



                    distance = nextDistance;


                }
                else
                {
                    var nextDistance = new Dictionary<AbstractState,
                        Tuple<uint,
                        SinglyLinkedList<AbstractEvent>,
                        Restriction>>(max);

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
                            w += s2.ActiveTasks();

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

                    distance = nextDistance;


                }

            }
            if (!distance.ContainsKey(target)) return null;
            var lst = distance[target].Item2.ToList();
            lst.Reverse();
            return lst;
        }


        public IEnumerable<AbstractEvent> TimedMaximumParallelism(
            DFA g,
            AbstractState initial,
            AbstractState target,
            int depth,
            Scheduler sch,
            Update update,
            Restriction res,
            Dictionary<AbstractState, Transition[]> transitions
            )
        {
            if (initial == null) initial = target;

            IDictionary<AbstractState, TimeContext> distance = new Dictionary<AbstractState, TimeContext>();
            distance.Add(
                initial,
                Tuple.Create(
                    SinglyLinkedList<AbstractEvent>.Empty,
                    sch,
                    res,
                    0f)
                );

            for (var i = 0; i < depth; i++)
            {
                if (distance.Count > limiar)
                {
                    var nextDistance = new ConcurrentDictionary<AbstractState, TimeContext>(
                        Environment.ProcessorCount,
                        distance.Count
                        );

                    Parallel.ForEach(Partitioner.Create(distance), kvp =>
                    {
                        var s = kvp.Key;
                        var d = kvp.Value;
                        var resA = d.Item3;
                        var schA = d.Item2;
                        var events = d.Item1;

                        var trans =
                            transitions[s].Where(t => t.IsControllableTransition
                            && resA[t.Trigger] > 0
                            && !update(schA, t.Trigger).Any(k => float.IsNaN(k.Value)))
                            .ToList();

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
                            w += s2.ActiveTasks();

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
                                t => t.IsControllableTransition
                                && resA[t.Trigger] > 0
                                && !update(schA, t.Trigger)
                                .Any(k => float.IsNaN(k.Value)))
                                .ToList();

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
                            w += s2.ActiveTasks();

                            var eventsB = events.Prepend(e);

                            var res2 = e.IsControllable ? new Restriction(resA) : resA;
                            if (e.IsControllable) res2[e]--;

                            var schB = update(schA, e);

                            if (schB.Any(k => float.IsNaN(k.Value))) continue;


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
}
