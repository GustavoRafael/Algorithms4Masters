

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
    .Dictionary <UltraDES.AbstractEvent, float>;

using Restriction = System.Collections.Generic.Dictionary <UltraDES.AbstractEvent, uint>;

using Update = System
    .Func<System.Collections.Generic.Dictionary <UltraDES.AbstractEvent, float>,
        UltraDES.AbstractEvent,
    System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>
    >;

using TimeContext = System.Tuple<sequecia_da_projecao_v3
    .SinglyLinkedList<UltraDES.AbstractEvent>, 
    System.Collections.Generic.Dictionary<UltraDES.AbstractEvent, float>,
    System.Collections.Generic.Dictionary
    <UltraDES.AbstractEvent, uint>,
    float>;
using TransitionNum = System.Tuple<byte, int>;  // entender seu uso



namespace sequecia_da_projecao_v3
{
    internal class Program
    {
        const int limiar = 100;

        private static readonly MyRandom Rnd = new MyRandom();

        private static void Main()
        {
            System.Threading.Thread.CurrentThread.Priority = System.Threading.ThreadPriority.AboveNormal;

            // GU-Comment: realiza apena um teste. Comentado para analise do codigo.
            Teste();
            Gu_Teste();
            
            // GU-Comment: Todos os testes do Lucas estão agrupados aki - testes_On = true libera sua execucão.
            bool testes_0n = false;
            if (testes_0n)
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

                Func<int, AbstractEvent[]>[] tests = new Func<int, AbstractEvent[]>[4];

                //Logical Algorithms

                tests[1] = (prod) => GreedyParallelism(
                    plant.Supervisor,
                    plant.InitialState,
                    plant.TargetState,
                    plant.Depth * prod,
                    plant.InitialScheduler,
                    plant.UpdateFunction,
                    plant.InitialRestrition(prod),
                    transitions
                    ).ToArray();

                tests[0] = (prod) => LogicalMaximumParallelism(
                    plant.Supervisor,
                    plant.InitialState,
                    plant.Depth * prod,
                    plant.TargetState,
                    plant.InitialRestrition(prod),
                    transitions
                    ).ToArray();

                //Timed Algorithms

                tests[2] = (prod) => GreedyTime(
                    plant.Supervisor,
                    plant.InitialState,
                    plant.TargetState,
                    plant.Depth * prod,
                    plant.InitialScheduler,
                    plant.UpdateFunction,
                    plant.InitialRestrition(prod),
                    transitions
                    ).ToArray();

                tests[3] = (prod) => TimedMaximumParallelism(
                    plant.Supervisor,
                    plant.InitialState,
                    plant.TargetState,
                    plant.Depth * prod,
                    plant.InitialScheduler,
                    plant.UpdateFunction,
                    plant.InitialRestrition(prod),
                    transitions
                    ).ToArray();
                /*
                tests[4] = (prod) => HeuristicShortestMakespan(
                    plant.Supervisor,
                    plant.InitialState,
                    plant.TargetState,
                    plant.Depth * prod,
                    plant.InitialScheduler,
                    plant.UpdateFunction,
                    plant.InitialRestrition(prod),
                    transitions
                    ).ToArray();
                    */

                // GU-Comment: Funções de contagem de tempo e paralelismo 

                Func<int, AbstractEvent[], float> time = (prod, seq) => TimeEvaluation(
                    plant.Supervisor,
                    plant.InitialState,
                    plant.TargetState,
                    seq,
                    plant.InitialScheduler,
                    plant.UpdateFunction,
                    plant.InitialRestrition(prod),
                    transitions
                    );

                Func<int, AbstractEvent[], float> paralell = (prod, seq) => ParallelismEvaluation(
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
                Console.ReadLine();

            }

        }

        private static void ShowResultado( List<(double time, AbstractEvent[] sequency, AbstractState[] dvstate)>indSel )
        {
            var ind_count = 1;
            foreach (var ss in indSel) //novosIndividuos)
            {
                //Console.Write("\n Makespan do Individuo {0} é  \n", ind_count2);
                Console.Write("\n\n Makespan do Individuo {0} é: {1} \n Div_states: ", ind_count, ss.time);

                foreach (var dv in ss.dvstate)      // imprimi os div states
                {
                    Console.Write(" {0}", dv);
                }
                Console.Write("\n\n");
                foreach (var ev in ss.sequency)
                {
                    Console.Write(" {0}", ev);
                }
                ind_count = ind_count + 1;
            }

        }

        // GU- Comment: Teste()- Esta função teste é chamada no main, mas apenas realiza o teste[0]. 
        // Nela é realiza o Timed Algorithms
        private static void Teste()
        {
            System.Threading.Thread.CurrentThread.Priority = System.Threading.ThreadPriority.AboveNormal;
            System.Threading.Thread.CurrentThread.CurrentCulture = new System.Globalization.CultureInfo("en-US");
            
            float maxIt = 20; //5;
            ISchedulingProblem plant = new SFM();

            var transitions = plant.Supervisor
                .Transitions.AsParallel()
                .GroupBy(t => t.Origin)
                .ToDictionary(gr => gr.Key, gr => gr.ToArray());

            Func<int, AbstractEvent[]>[] tests = new Func<int, AbstractEvent[]>[4];


            //Timed Algorithms

            tests[0] = (prod) => TimedMaximumParallelism(
                   plant.Supervisor,
                   plant.InitialState,
                   plant.TargetState,
                   plant.Depth * prod,
                   plant.InitialScheduler,
                   plant.UpdateFunction,
                   plant.InitialRestrition(prod),
                   transitions
                   ).ToArray();

            tests[1] = (prod) => GreedyParallelism(
                    plant.Supervisor,
                    plant.InitialState,
                    plant.TargetState,
                    plant.Depth * prod,
                    plant.InitialScheduler,
                    plant.UpdateFunction,
                    plant.InitialRestrition(prod),
                    transitions
                    ).ToArray();
            tests[2] = (prod) => HeuristicShortestMakespan(
                    plant.Supervisor,
                    plant.InitialState,
                    plant.TargetState,
                    plant.Depth * prod,
                    plant.InitialScheduler,
                    plant.UpdateFunction,
                    plant.InitialRestrition(prod),
                    transitions
                    ).ToArray();
            tests[3] = (prod) => GreedyTime(
                   plant.Supervisor,
                   plant.InitialState,
                   plant.TargetState,
                   plant.Depth * prod,
                   plant.InitialScheduler,
                   plant.UpdateFunction,
                   plant.InitialRestrition(prod),
                   transitions
                   ).ToArray();
            /*
            tests[4] = (prod) => LogicalMaximumParallelism(
                plant.Supervisor,
                plant.InitialState,
                plant.Depth * prod,
                plant.TargetState,
                plant.InitialRestrition(prod),
                transitions
                ).ToArray();
                */

            Func<int, AbstractEvent[], float> time = (prod, seq) => TimeEvaluation(
                plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                seq, //.Where(e1 => e1.IsControllable).ToArray(),
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(prod),
                transitions
                );

            Func<int, AbstractEvent[], float> paralell = (prod, seq) => ParallelismEvaluation(
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
            int count = 0;
            //AbstractEvent q;

            // realização dos teste acima simplificado
            bool testes2_0n = true; // controla a habilitação do teste abaixo
            bool testes2_0ff = false; // controla a habilitação do teste abaixo
            if (testes2_0ff)
            {
                foreach (var test in tests)
                {
                    Console.WriteLine("\n-------------------------------------\n");

                    foreach (var products in new[] { 7})//1, 5, 10, 50, 100, 500, 1000 })
                    {
                        var lst = new List<AbstractEvent[]>();
                        Stopwatch timer = new Stopwatch();
                        timer.Start();
                        for (var it = 0; it < maxIt; it++) // maxIt: numero de vezes que uma sequencia é gerada
                            lst.Add(test(products));
                        timer.Stop();
                        /*
                        Console.Write(" sequencia gerada \n");
                        foreach (var pr in lst.ToArray()[count])
                        {
                            //Console.Write(" {0}", pr );
                            if (pr.IsControllable) Console.Write(" {0}", pr);
                        }
                        Console.Write("\n");
                        */
                        var divStates = TimeDivStatesEvaluation(
                            plant.Supervisor,
                            plant.InitialState,
                            plant.TargetState,
                            lst.First().ToArray(),              // sequencia 
                            plant.InitialScheduler,
                            plant.UpdateFunction,
                            plant.InitialRestrition(products),
                            transitions
                            );

                        var makespan = lst.Select(s => time(products, s)).Average();
                        var parallelism = lst.Select(s => paralell(products, s)).Average();
                        var optimizationTime = timer.ElapsedMilliseconds / maxIt;
                        var seqSize = lst.ToArray()[0].Count();
                        var numDvStates = divStates.dvstate.Count();

                        Console.Write("{{{0},{1},{2},{3},{4},{5}}}, \n ",
                            products,
                            optimizationTime,
                            float.IsNaN(makespan) ? -1.0f : makespan,
                            parallelism,
                            seqSize,
                            numDvStates);
                    }
                    count = count + 1;
                }
            }

            // imprime o tempo de uma seq de um arquivo
            //ReadFileSeqTimed(plant, transitions,"lucasSeq.txt",8);

            // **************************************************************************************************************************************************
        }

        private static void ReadFileSeqTimed( ISchedulingProblem plant, Dictionary<AbstractState, Transition[]> transit, string fileName, int product )
        {
            // leitura da sequencia do lucas - 
            Dictionary<int, Event> ee = new[]
            {
                11, 12, 21, 22, 41,
                42, 51, 52, 53, 54, 31,
                32, 33, 34, 35, 36, 37, 38, 39, 30, 61,
                63, 65, 64, 66, 71, 72, 73, 74, 81, 82
            }.ToDictionary(alias => alias,
                    alias =>
                        new Event(alias.ToString(),
                            alias % 2 == 0 ? Controllability.Uncontrollable : Controllability.Controllable));

            // "lucasSeq.txt"
            var lines = File.ReadAllLines(fileName).Select(a => a.Split(','));
            var llSeq = new List<AbstractEvent>();

            //var csv = from line in lines select (from piece in line  select piece);
            var sqq = lines.ToList();

            foreach (var sq in sqq[0])
            {
                llSeq.Add(ee[Convert.ToInt32(sq)]);
            }

            var divStates = TimeDivStatesEvaluation(plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                llSeq.ToArray(),
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(product),
                transit
                );
            var avlObj = AvaliaObjetivo(
                    llSeq.ToArray().Where(e1 => e1.IsControllable).ToArray(),
                    plant.InitialScheduler,
                    plant.InitialRestrition(product),
                    plant.UpdateFunction,
                    plant.InitialState,
                    transit,
                    divStates.dvstate);

            var paral = ParallelismEvaluation(
                    plant.Supervisor,
                    plant.InitialState,
                    plant.InitialState,
                    llSeq.ToArray(),
                    plant.InitialScheduler,
                    plant.UpdateFunction,
                    plant.InitialRestrition(product),
                    transit
                    );
            var paralGU = ParallelismEvaluation(
                   plant.Supervisor,
                   plant.InitialState,
                   plant.InitialState,
                   avlObj.sequency,
                   plant.InitialScheduler,
                   plant.UpdateFunction,
                   plant.InitialRestrition(product),
                   transit
                   );

            var tempo = TimeEvaluation(
                plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                llSeq.ToArray(),
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(product),
                transit
                );
            Console.Write("\n A sequencia do arquivo ( {0} ) possui o tempo de {1}, TG {2}, paralelismo {3}, paral GU {4} num divStates {}\n", fileName,tempo, avlObj.time, paral, paralGU, divStates.dvstate.Count());
        }

        private static void WriteFileSeqTimed( double[] evTime, AbstractEvent[] [] events, string fileName)
        {
            // salva no diretório escolhido
            System.Threading.Thread.CurrentThread.CurrentCulture = new System.Globalization.CultureInfo("en-US");
            var file_name = fileName;                            // rept.ToString() +"_SFM_8A_8B_sequency_data.csv";
            using (var file = File.CreateText(file_name))
            {
                for (int i = 0; i < evTime.Length; i++)
                {
                    file.Write(evTime[i].ToString());
                    file.Write('-');
                    foreach (var ev in events[i])
                    {
                        file.Write(ev.ToString());
                        file.Write(',');
                    }
                    file.Write('\n');

                }
            }
        }


        private static void Gu_Teste()
        {
            System.Threading.Thread.CurrentThread.Priority = System.Threading.ThreadPriority.AboveNormal;
            System.Threading.Thread.CurrentThread.CurrentCulture = new System.Globalization.CultureInfo("en-US");

            //---------------------------------
            // geração do automato da projeção
            // --------------------------------
            ISchedulingProblem plant2 = new SF();

            var p1 = plant2.Supervisor.simplifyName();
            var p1r = plant2.Supervisor.Trim;
            plant2.Supervisor.showAutomaton();
       
            var proj = plant2.Supervisor.Projection(plant2.Supervisor.Events.Where(ev => ev.IsControllable == false));
            proj.simplifyName();
            var e =
              Enumerable.Range(0, 8)
                  .Select(i =>
                      new Event(i.ToString(),
                          i % 2 != 0
                              ? Controllability.Controllable
                              : Controllability.Uncontrollable)
                  ).ToArray();

            State s0 = new State("s0", Marking.Unmarked);
            State s1 = new State("s1", Marking.Unmarked);
            //State s2 = new State("s2", Marking.Unmarked);
            State s2 = new State("s2", Marking.Marked);

           // Creating an Automaton
            var G = new DeterministicFiniteAutomaton(new[]
            {
                new Transition(s0, e[7], s1),
                new Transition(s1, e[7], s2),
                //new Transition(s2, e[5], s3)
            }, s0, "G");

            var aut = proj.ParallelCompositionWith(G).Trim;
            aut.simplifyName();
            aut.showAutomaton("proj_comp");
            
            proj.showAutomaton();

            
            // --------------------------------
            //          inicio do clonal
            // --------------------------------

            ISchedulingProblem plant1 = new SFM();
            var transitions1 = plant1.Supervisor
                .Transitions.AsParallel()
                .GroupBy(t => t.Origin)
                .ToDictionary(gr => gr.Key, gr => gr.ToArray());

            // teste do clonal
            int prodA = 1;
            
            // parâmetros 
            
            var pbtState = 0.90;                // probabilidade de troca aleatéoria no estado divergente
            // var pcpreserveSeq = 0.30; cada pai possui um percentual proprio de preservação da sequencia e os  filhos herdam essa caracteristica.
            int indPolulacao = 20;
            int numIndividuosMutados = 10;
            int maxGeracoes = 60;              // numero máximo de gerações 
            int indSelecGeracao = 2;            // novos individuos
            int GeracaoSemMelhorasMax = 10;     // numero de gerações sem melhoras
            string[] src = { "randInd", "TMP", "HMP", "LMP" };
            int numMaxRept = 10;
            var data = new List<(double time, int iter, double medMakespam, int nGeracoes)>();

            // tempo total
            var timerTotal = new Stopwatch();
            timerTotal.Start();
            Console.Write($"\n\n  -- NumProdutos: A = B = {prodA} --\n");

            foreach (var sc in src)
            {
                Console.Write($"\n\n Metodo: {sc}\n");

                // (double time, AbstractEvent[] sequency, AbstractState[] dvState)[] copyResult;
                data.Clear();
                for (int rept = 0; rept < numMaxRept; rept++)
                {
                    // escopo do metodo clonal 
                    var timer1 = new Stopwatch();
                    timer1.Start();
                    
                    var result = CLONAL(
                        plant1,
                        prodA,
                        transitions1,
                        pbtState,
                        //pcpreserveSeq,
                        indPolulacao,
                        numIndividuosMutados,
                        maxGeracoes,
                        indSelecGeracao,
                        GeracaoSemMelhorasMax,
                        sc
                        );
                    /*
                    var result = Enumerable.Range(0, numMaxRept)
                        .AsParallel()
                        .Select(i => CLONAL(
                            plant1,
                            prodA,
                            transitions1,
                            pbtState,
                            //pcpreserveSeq,
                            indPolulacao,
                            numIndividuosMutados,
                            maxGeracoes,
                            indSelecGeracao,
                            GeracaoSemMelhorasMax,
                            sc)
                        ).ToArray();
                    */
                    //showResultado(indSelecionados);
                    timer1.Stop();
                    //Console.Write($"\n Otimização finalizada em {timer1.ElapsedMilliseconds} mili-segundos. \n");
                    //var mks = result.Select(idt => idt.Item1.Select(ms => ms.time).Min()).Min();
                    var medMakespam = result.Item1.Select(idt => idt.time).Min();
                    //var seqTam = result.Item1.Where(sw => sw.time == medMakespam).Select(stw => stw.sequency).ToArray()[0].Count();
                    /*
                    var tl = result.Item1.Where(sw => sw.time == medMakespam).Select(stw => TimeEvaluation(
                        plant1.Supervisor,
                        plant1.InitialState,
                        plant1.TargetState,
                        stw.sequency, //.Where(e1 => e1.IsControllable).ToArray(),
                        plant1.InitialScheduler,
                        plant1.UpdateFunction,
                        plant1.InitialRestrition(prodA),
                        transitions1
                        )).Min();
                    // check numero de estados divergentes
                    
                    var bestSeq = result.Item1.Where(sw => sw.time == medMakespam).ToArray()[0];
                    var divStatesChecking = TimeDivStatesEvaluation(
                       plant1.Supervisor,
                       plant1.InitialState,
                       plant1.InitialState,
                       bestSeq.sequency,
                       plant1.InitialScheduler,
                       plant1.UpdateFunction,
                       plant1.InitialRestrition(prodA),
                       transitions1
                       );
                    
                    var parall = result.Item1.Select(idt => ParallelismEvaluation(
                        plant1.Supervisor,
                        plant1.InitialState,
                        plant1.InitialState,
                        idt.sequency,
                        plant1.InitialScheduler,
                        plant1.UpdateFunction,
                        plant1.InitialRestrition(prodA),
                        transitions1
                        )).Average();
                    */
                    // prints antigos por execução
                    var numGeracoes = result.numeroTotalGeracoes;
                    data.Add((timer1.ElapsedMilliseconds, result.numAvalfobj, medMakespam, numGeracoes));

                    // inicio - Console.Write($"\n Avaliação {rept + 1}/{numMaxRept}, mks: {medMakespam}, tempo Lucas {tl}, paralelismo {Math.Round(parall, 0)}, num divSates {divStatesChecking.dvstate.Count()},numGeracoes {numGeracoes}, Tamanho da sequencia {seqTam},tempo (ms): {timer1.ElapsedMilliseconds}");
                    // ultimo - Console.Write($"\n Avaliação {rept + 1}/{numMaxRept}, mks: {medMakespam}, paralelismo {Math.Round(parall, 0)}, numGeracoes {numGeracoes}, tempo (ms): {timer1.ElapsedMilliseconds}");
                    
                    // novos prints
                    //var numGeracoes = result.Select(ng => ng.numeroTotalGeracoes).Min();
                    //data.Add((timer1.ElapsedMilliseconds, result.Select(na => na.numAvalfobj).Min(), mks, numGeracoes));
                }


                //Console.Write($"\n\n Tempo médio Otimização {data.Select(ck => ck.time).Average()} ms/exe \n");

                //Console.Write($"\n Numero de iteracoes médio {data.Select(ni => ni.iter).Average()}, numero de produtos: A = B = {prodA}");

                //Console.Write($"\n Numero medio de gerações {data.Select(ng => ng.nGeracoes).Average()}");
                Console.Write($"\n TimeMedOtm (ms/exe): {data.Select(ck => ck.time).Average()},  NumMedIter {data.Select(ni => ni.iter).Average()}, NumMedGer {data.Select(ng => ng.nGeracoes).Average()}");

                Console.Write($"\n Makespam min {data.Select(mk => mk.medMakespam).Min()}, " +
                    $"Makespam medio {Math.Round(data.Select(mk => mk.medMakespam).Average(), 2)}, Makespam Max {data.Select(mk => mk.medMakespam).Max()}\n");
            }

            timerTotal.Stop();
            Console.Write($"\n\n Tempo total (s): {timerTotal.Elapsed}");           
            Console.Write("\n\n Sequencia final \n");
            Console.Write(" Fim da otimização \n");

            // fin 
            Console.ReadLine();
        }

        // contador de tempo do lucaas
        private static float TimeEval(DFA S, AbstractState initial, AbstractState destination,
            AbstractEvent[] sequence, Scheduler sch, Update update, Restriction res)
        {
            var transitions = S.Transitions.AsParallel()
                .GroupBy(t => t.Origin)
                .ToDictionary(gr => gr.Key, gr => gr.ToArray());

            res = new Restriction(res);

            var state = initial;
            var events = new List<AbstractEvent>();

            float time = 0;

            foreach (var e in sequence)
            {
                var trans = transitions[state].Where(t => (t.Trigger.IsControllable && res[t.Trigger] > 0) || !t.Trigger.IsControllable).First(t => t.Trigger == e);//.Single(t => t.Trigger == e);

                state = trans.Destination;

                events.Add(e);

                if (e.IsControllable) res[e]--;
                time += sch[e];
                sch = update(sch, e);
            }

            return state == destination ? time : float.PositiveInfinity;
        }

        // GU: Algoritmo de seleção clonal

        private static ((double time, AbstractEvent[] sequency, AbstractState[] dvState)[], int numAvalfobj, int numeroTotalGeracoes) CLONAL(
            ISchedulingProblem p1,
            int prodA,
            Dictionary<AbstractState, Transition[]> transicoes,
            double pbtState,
            //double pcpreserveSeq,
            int indPolulacao = 20,
            int numIndMutados = 5,
            int numMaxGeracoes = 10,
            int SelecIndGeracao = 1,
            int numGeracaoSemMelhorasMax = 30,
            string source = "randInd"
           )
        {
            //var timer = new Stopwatch();
            //timer.Start();
            var numAvalfObj = 0;
            var jaAvaliados = new HashSet<(double time, AbstractEvent[] sequency, AbstractState[] dvstate)>();

            var individuosAleatorios = new List<(double time, AbstractEvent[] sequency, AbstractState[] dvstate)>();
            var divZero = new List<AbstractState>().ToArray();
            switch (source)
            {
                case "randInd":
                    // valor default indPopulacao = 10
                    individuosAleatorios = Enumerable.Range(0, 2 * indPolulacao)
                        .AsParallel()
                        .Select(i => SequenciaAleatoria(
                            p1.Depth * (prodA),
                            p1.InitialScheduler,
                            p1.InitialRestrition(prodA),
                            p1.InitialState,
                            p1.TargetState,
                            transicoes))
                        .ToList();
                    break;

                case "LMP":                  
                    var seqs = Enumerable.Range(0, 2 * indPolulacao)
                            .AsParallel()
                            .Select(i => LogicalMaximumParallelism(
                                p1.Supervisor,
                                p1.InitialState,
                                p1.Depth * prodA,
                                p1.TargetState,
                                p1.InitialRestrition(prodA),
                                transicoes));
                    /*
                       LogicalMaximumParallelism(
                                p1.Supervisor,
                                p1.InitialState,
                                p1.Depth * prodA,
                                p1.TargetState,
                                p1.InitialRestrition(prodA),
                                transicoes)
                    */
                    foreach (var idv in seqs)
                    //for ( int iv = 0; iv < 2 * indPolulacao; iv++ )
                    {
                        individuosAleatorios.Add((
                            0.0,
                            idv.Where(lp => lp.IsControllable).ToArray(),
                            divZero));
                    }
                    break;

                case "TMP":
                    
                    var seqsTMP = Enumerable.Range(0, 2 * indPolulacao)
                        .AsParallel()
                        .Select(i => TimedMaximumParallelism(
                            p1.Supervisor,
                            p1.InitialState,
                            p1.TargetState,
                            p1.Depth * prodA,
                            p1.InitialScheduler,
                            p1.UpdateFunction,
                            p1.InitialRestrition(prodA),
                            transicoes
                        ));
                    foreach(var idv in seqsTMP)
                    {
                        individuosAleatorios.Add(( 
                            0.0,
                            idv.Where(lp => lp.IsControllable).ToArray(),
                            divZero));                        
                    }
                    /*
                    for (int iv = 0; iv < 2 * indPolulacao; iv++)
                    {
                        individuosAleatorios.Add((
                            0.0,
                            TimedMaximumParallelism(
                            p1.Supervisor,
                            p1.InitialState,
                            p1.TargetState,
                            p1.Depth * prodA,
                            p1.InitialScheduler,
                            p1.UpdateFunction,
                            p1.InitialRestrition(prodA),
                            transicoes).Where(lp => lp.IsControllable).ToArray(),
                            divZero));
                    }*/
                    break;

                case "HMP":
                    var seqsHMP = Enumerable.Range(0, 2 * indPolulacao)
                        .AsParallel()
                        .Select(i => HeuristicShortestMakespan(
                            p1.Supervisor,
                            p1.InitialState,
                            p1.TargetState,
                            p1.Depth * prodA,
                            p1.InitialScheduler,
                            p1.UpdateFunction,
                            p1.InitialRestrition(prodA),
                            transicoes
                        ));
                    foreach (var idv in seqsHMP)
                    {
                        individuosAleatorios.Add((
                            0.0,
                            idv.Where(lp => lp.IsControllable).ToArray(),
                            divZero));
                    }
                    break;
            }

            
            
            // GU: calcula o makespan, com controle de seleção do número de melhores indivíduos selecionados
            var indSelecionados = individuosAleatorios
                .AsParallel()
                .Select(ind => AvaliaObjetivo(
                    ind.sequency,
                    p1.InitialScheduler,
                    p1.InitialRestrition(prodA),
                    p1.UpdateFunction,
                    p1.InitialState,
                    transicoes,
                    ind.dvstate))
                .Where(s1 => s1.time != 1234)
                .OrderBy(seq=> seq.time)
                .Take(Convert.ToInt32(individuosAleatorios.Count() * 0.50))
                .ToList();

            numAvalfObj += indSelecionados.Count();


            var novosIndividuos = new List<(double time, AbstractEvent[] sequency, AbstractState[] dvstate)>();
            // GU: 05/02/2018 - pos reunição: implementar numero de geração se melhoras
            int numGeracaoSemMelhoras = 0;
            int numeroTotalGeracoes = 0;

            double menorMakespanAtual = indSelecionados.Select(msp => msp.time).Min();
            double menorMakespamMedido;
            
            //GU:05/02/2018 -
            var novaGeracao = new List<(double time, AbstractEvent[] sequency, AbstractState[] dvstate)>();

            while (numGeracaoSemMelhoras < numGeracaoSemMelhorasMax && numeroTotalGeracoes < numMaxGeracoes)
            {

                //(double time, double pcPreserveSeq, AbstractEvent[] sequency, AbstractState[] dvstate) sInd;

				// GU-11/02/2018:  
				var numIntervalo = indSelecionados.Count;
                var incremento = 1.00 / numIntervalo;//Math.Round(1.00/numIntervalo,2);
				Double acumula = 0.0;
				acumula = acumula + incremento;
				
                foreach (var sInd in indSelecionados)
                {
                    // evita availar individuos repetidos
                    if (!jaAvaliados.Contains(sInd))
                    {
                        jaAvaliados.Add(sInd);
						var ppseq = 0.8 - acumula;
                        var pcIndMut = 1.0 - acumula < 0.05 ? 0.05 : 1.1 - acumula;
                        // GU: Gera novos indivíduos filhos (de acordo com o numInividuos), a partir de uma sequencia pai sInd
                        // valor default numIndividuosMutados = 5;
                        novosIndividuos = Enumerable.Range(0, Convert.ToInt32((Math.Round(pcIndMut, 2))*numIndMutados))  // gera indivíduos proporcional ao rank da sua solução (1º tem mais filhos os ultimo tem menos)
                            .AsParallel()
                            .Select(i => MutaGen(
                                p1.Depth * (prodA),
                                sInd.sequency,
                                p1.InitialScheduler,
                                p1.InitialRestrition(prodA),
                                p1.UpdateFunction,
                                p1.InitialState,
                                p1.TargetState,
                                transicoes,
                                sInd.dvstate,
                                pbtState,
								Math.Round(ppseq < 0.0 ? 0.0 : ppseq,2)
                                //sInd.pcPreserveSeqAV
                                ))
                                .Where(se => se.time != 1234)
                                .OrderBy(seq => seq.time)
								.Take(SelecIndGeracao)                                      // são selecionados os N primeiros indivívduos (N = numero de indivíduos)
                                .ToList();
                                
                        numAvalfObj += novosIndividuos.Count();
						acumula = acumula + incremento;

                        //GU: adiciona os melhores individuos a conjuntos das soluções não dominadas e pega os 80% m
                        //GU: 05/fev/2018 - a partir de sugestão da professora serão selecionados os melhores filhos e adicionados ao conjunto de soluções                         
                        novaGeracao = novaGeracao.Union(novosIndividuos).ToList();
                    }
                    else
                    {
                        if (sInd.time < menorMakespanAtual)
                        {
                            numAvalfObj += 1;
                            novaGeracao.Add(sInd); //novaGeracao.Union(sInd).ToList();
                        }
						acumula = acumula + incremento;
                        continue;
                    }
                    
                }
                //jaAvaliados.Clear();
                //GU: 05/02/2018 - Avalia se houve melhora ou não
                menorMakespamMedido = novaGeracao.Select(msp => msp.time).Min();
                if (menorMakespamMedido < menorMakespanAtual)
                {
                    menorMakespanAtual = menorMakespamMedido;
                    numGeracaoSemMelhoras = 0;
                    ++numeroTotalGeracoes;
                }
                else
                {
                    ++numGeracaoSemMelhoras;
                    ++numeroTotalGeracoes;
                }
                // GU: passa os n
                //indSelecionados = novaGeracao;
				indSelecionados = novaGeracao.OrderBy(seq => seq.time)
                    .Take(indPolulacao)
				    .ToList();
                novaGeracao.Clear();
            }
            // termina mutaGen
            return (indSelecionados.ToArray(),numAvalfObj,numeroTotalGeracoes);            
        }


        // GU: gera mutações nos indivíduos de acordo com uma probabilidade
        private static (double time, AbstractEvent[] sequency, AbstractState[] dvstate) MutaGen(
            int depth,
            AbstractEvent[] seqProj,
            Scheduler schMG,
            Restriction resMG,
            Update update,
            AbstractState inicial,
            AbstractState target,
            Dictionary<AbstractState, Transition[]> transitions,
            AbstractState[] dvState,
            double pbtState = 0.1,
            double pcpreserveSeq = 0.8              // qdo criada todos os individuos tinha valores fixos. Agora são aleatórios
            )
        {

            double tempo = 0;

            var newSeq = new List<AbstractEvent>();
            var estado = inicial;
            //var seqOriginal = new List<AbstractEvent>(seqProj);

            var seqOriginal = seqProj.ToList();

            var selectDivStates = dvState.Take(Convert.ToInt32(dvState.Count() * pcpreserveSeq)).ToList();
            var newDivState = new List<AbstractState>();

            var evento = seqOriginal.First();
            var nextEvent = 0;
            while (!selectDivStates.IsEmpty())
            {
                var trans = transitions[estado].Where(t => t.IsControllableTransition && resMG[t.Trigger] > 0).ToList();

                // trata os eventos controlaveis
                if (trans.Any(t => t.Trigger.IsControllable && t.Trigger == seqProj[nextEvent]))
                {

                    // armazena os estados divergentes
                    if (trans.Count > 1 && trans.All(tr => tr.IsControllableTransition) && selectDivStates.Contains(estado))
                    {
                        newDivState.Add(estado);
                        selectDivStates.Remove(estado);
                    }

                    newSeq.Add(seqProj[nextEvent]);

                    if (seqProj[nextEvent].IsControllable) resMG[seqProj[nextEvent]]--;  // res[e] --  reduz a quantidade eventos relativa ao numero de produtos.
                    tempo += schMG[seqProj[nextEvent]];
                    schMG = update(schMG, seqProj[nextEvent]);

                    estado = trans.Single(t => t.Trigger == seqProj[nextEvent]).Destination;
                }
                else // trata os eventos não controláveis 
                {
                    trans = transitions[estado].Where(t => !t.IsControllableTransition && t.Trigger == seqProj[nextEvent]).ToList();

                    estado = trans.Single(t => t.Trigger == seqProj[nextEvent]).Destination;

                    newSeq.Add(seqProj[nextEvent]);
                    tempo += schMG[seqProj[nextEvent]];
                    schMG = update(schMG, seqProj[nextEvent]);
                }

                nextEvent++; // incrementa o proximo evento na lista
            }

            var newDepth = newSeq.Count();

            // Mutação no resto da sequencia
            Transition transicao;
            for (var k = newDepth; k < depth; k++)
            {
                var trans = transitions[estado].Where(t => t.IsControllableTransition && resMG[t.Trigger] > 0).ToList();
                var trans2 = transitions[estado].Where(t => !t.IsControllableTransition).ToList();

                // qdo eventos controláveis modificam o tempo SFM 61,63,65

                if (trans.Any(ts => ts.IsControllableTransition && schMG[ts.Trigger] > 0 && resMG[ts.Trigger] > 0))
                {
                    var tminAV = transitions[estado]
                        .Where(t => t.IsControllableTransition && resMG[t.Trigger] > 0 && schMG[t.Trigger] > 0 || !t.IsControllableTransition)
                        .Select(t2 => schMG[t2.Trigger])
                        .Min();
                    var transicao1 = transitions[estado].First(t => schMG[t.Trigger] == tminAV);

                    tempo += schMG[transicao1.Trigger];

                    schMG = update(schMG, transicao1.Trigger);
                    newSeq.Add(transicao1.Trigger);
                    estado = transicao1.Destination;

                    if (transicao1.Trigger.IsControllable) resMG[transicao1.Trigger]--;

                    continue;
                }

                // qdo não houver evento c ou nc pra ocorrer
                if (transitions[estado].Where(tw => tw.IsControllableTransition && resMG[tw.Trigger] > 0 || !tw.IsControllableTransition).Count() == 0)
                {
                    var minSCH = schMG.Where(ag => !ag.Key.IsControllable && !float.IsInfinity(ag.Value)).Select(ag2 => ag2.Value).Min();
                    var schEvent = schMG.Where(ec => ec.Value == minSCH).Select(eh => eh.Key).First();

                    if (schEvent.IsControllable) resMG[schEvent]--;

                    tempo += schMG[schEvent];

                    schMG = update(schMG, schEvent);
                    newSeq.Add(schEvent);

                    continue;
                }

                if (!trans.Any())
                {
                    var tminMG = transitions[estado].Where(t => !t.IsControllableTransition).Select(t => schMG[t.Trigger]).Min();
                    trans = transitions[estado].Where(t => !t.IsControllableTransition && schMG[t.Trigger] == tminMG).ToList();

                    transicao = trans.Random(Rnd);

                    tempo += schMG[transicao.Trigger];

                    schMG = update(schMG, transicao.Trigger);
                    newSeq.Add(transicao.Trigger);
                    estado = transicao.Destination;

                    continue;
                }

                // armazena os novos estados divergentes
                if (trans.Count > 1 && trans.All(tr => tr.IsControllableTransition))
                {
                    newDivState.Add(estado);

                    transicao = Rnd.NextDouble() < pbtState
                        ? trans.Random(Rnd)
                        : trans.First();

                    if (transicao.Trigger.IsControllable) resMG[transicao.Trigger]--;

                    tempo += schMG[transicao.Trigger];

                    schMG = update(schMG, transicao.Trigger);
                    newSeq.Add(transicao.Trigger);
                    estado = transicao.Destination;
                }
                else if (trans.Count == 1 && resMG[trans.Select(te => te.Trigger).First()] > 0)
                {
                    transicao = trans.First();
                    if (transicao.Trigger.IsControllable) resMG[transicao.Trigger]--;

                    tempo += schMG[transicao.Trigger];

                    schMG = update(schMG, transicao.Trigger);
                    newSeq.Add(transicao.Trigger);
                    estado = transicao.Destination;
                }
                else
                {
                    k--;
                }


            }

            // completa os eventos nao controláveis q ainda existem apos o fim do while
            while (schMG.Select(ind => !ind.Key.IsControllable && !float.IsInfinity(ind.Value)).Any(s => s))
            {
                var tmin = transitions[estado].Where(t => !t.IsControllableTransition).Select(t => schMG[t.Trigger]).Min();
                var transicao1 = transitions[estado].First(t => !t.IsControllableTransition && schMG[t.Trigger] == tmin);

                tempo += schMG[transicao1.Trigger];

                schMG = update(schMG, transicao1.Trigger);
                newSeq.Add(transicao1.Trigger);
                estado = transicao1.Destination;
            }

            if (estado != inicial) tempo = 1234; //throw new Exception("A busca deve chegar a um estado marcado");

            //return (tempo, newSeq.Where(e => e.IsControllable).ToArray(), newDivState.ToArray());
            return (tempo,  newSeq.ToArray(), newDivState.ToArray());
        }

        // GU: gera sequências aleatórias (indivíduos)
        public static (double time, AbstractEvent[] sequency, AbstractState[] dvstate) SequenciaAleatoria(
            int depth,
            Scheduler schSA,
            Restriction resSA,
            AbstractState inicial,
            AbstractState target,
            Dictionary<AbstractState, Transition[]> transitions
            )
        {
            var tempo = 0.0;
            var seq = new List<AbstractEvent>();
            var dstate = new List<AbstractState>();
            var estado = inicial;
            for (var k = 0; k < depth; k++)
            {
                var trans = transitions[estado].Where(t => t.IsControllableTransition && resSA[t.Trigger] > 0).ToList();

                
                // qdo aparece eventos q modificam o tempo 61,63,65
                if (trans.Any(ts => ts.IsControllableTransition && schSA[ts.Trigger] > 0 ))
                {
                    var tminSA = transitions[estado]
                        .Where(t => t.IsControllableTransition && resSA[t.Trigger] > 0 && schSA[t.Trigger] > 0 || !t.IsControllableTransition)
                        .Select(t2 => schSA[t2.Trigger])
                        .Min();
                    var transicao1 = transitions[estado].First(t => schSA[t.Trigger] == tminSA);

                    //sch = update(sch, transicao1.Trigger);
                    seq.Add(transicao1.Trigger);
                    estado = transicao1.Destination;

                    if (transicao1.Trigger.IsControllable) resSA[transicao1.Trigger]--;

                    continue;                 
                }
                

                if (!trans.Any())
                {
                    if (transitions[estado].All(t => t.IsControllableTransition)) break; // se só tem eventos controlaveis (mas não são permitidos)

                    var tmin = transitions[estado].Where(t => !t.IsControllableTransition ).Select(t => schSA[t.Trigger]).Min();
                    trans = transitions[estado].Where(t => !t.IsControllableTransition && schSA[t.Trigger] == tmin ).ToList();
                }

                // armazena os estados divergentes
                if (trans.Count() > 1 && trans.Where(tr => tr.IsControllableTransition).Count() > 1)
                //if (trans.Count>1 && trans.All(tr=> tr.IsControllableTransition))
                {
                    dstate.Add(estado);
                }

                var transicao = trans.Random(Rnd);

                if (transicao.Trigger.IsControllable)
                {
                    resSA[transicao.Trigger]--;
                }

                seq.Add(transicao.Trigger);
                estado = transicao.Destination;
            }

            if (estado != inicial) throw new Exception("A busca deve chegar a um estado marcado");

           // var preservaSeq = Rnd.NextDouble();
            
            return (tempo, seq.Where(e => e.IsControllable).ToArray(), dstate.ToArray());
            //return (seq.ToArray(), dstate.ToArray()); // aguardando melhor solução
        }

        // GU: calcula o makespan da sequencia passada (de um indivíduo)- comprar com a outra que conta o tempo
        private static (double time, AbstractEvent[] sequency, AbstractState[] dvstate) AvaliaObjetivo(
            AbstractEvent[] ncseqProj,
            Scheduler schAV,
            Restriction resAV,
            Update update,
            AbstractState inicial,
            Dictionary<AbstractState, Transition[]> transitions,
            AbstractState [] dvstate
            )
        {
            double tempo = 0;
            var seqAval = new List<AbstractEvent>();
            var estado = inicial;
            var seqProj = ncseqProj.Select(t=> t).Where(e => e.IsControllable).ToArray();
            var newDvstate = new List<AbstractState>();

            for (var k = 0; k < seqProj.Length; k++)
            {
                var trans = transitions[estado].Where(t => t.IsControllableTransition && resAV[t.Trigger] > 0).ToList();
                var transAV = transitions[estado].Where(t =>  !t.IsControllableTransition ).ToList();

                // qdo aparece eventos q modificam o tempo 61,63,65
                if (trans.Any(ts => ts.IsControllableTransition && schAV[ts.Trigger] > 0 && ts.Trigger == seqProj[k]))
                {
                    var tminAV = transitions[estado]
                        .Where(t => t.IsControllableTransition && resAV[t.Trigger] > 0 && schAV[t.Trigger] > 0 || !t.IsControllableTransition)
                        .Select(t2 => schAV[t2.Trigger])
                        .Min();
                    var transicao1 = transitions[estado].First(t => schAV[t.Trigger] == tminAV);

                    
                    tempo += schAV[transicao1.Trigger];

                    schAV = update(schAV, transicao1.Trigger);
                    seqAval.Add(transicao1.Trigger);
                    estado = transicao1.Destination;

                    if (transicao1.Trigger.IsControllable) resAV[transicao1.Trigger]--;

                    if (transicao1.Trigger == seqProj[k])
                    {
                        continue;
                    }
                    else
                    {
                        k--;
                        continue;
                    }                                       
                }

                // executa um evento não controlável, caso não seja possivel realizar um evento da sequencia original  
                if (trans.All(t => t.Trigger != seqProj[k]))
                {
                    if (transitions[estado].All(t => t.IsControllableTransition)) continue; // se só tem eventos controlaveis (mas não são permitidos)

                    var tminAV = transitions[estado].Where(t => !t.IsControllableTransition ).Select(t2 => schAV[t2.Trigger] ).Min();
                    var transicao1 = transitions[estado].First(t => !t.IsControllableTransition && schAV[t.Trigger] == tminAV);
                                        
                    tempo += schAV[transicao1.Trigger];
                   
                    schAV = update(schAV, transicao1.Trigger);
                    seqAval.Add(transicao1.Trigger);
                    estado = transicao1.Destination;

                    k--;
                    continue;
                }

                // armazena os estados divergentes
                if (trans.Count() > 1 && trans.Where(tr => tr.IsControllableTransition).Count() > 1) // teste gu 1/02/2018
                {
                    newDvstate.Add(estado);
                }
                // executa o evento controlável q não possui restrição 
                var transicao2 = trans.Single(t => t.Trigger == seqProj[k]);

                tempo += schAV[transicao2.Trigger];
                
                resAV[transicao2.Trigger]--;
                schAV = update(schAV, transicao2.Trigger);

                seqAval.Add(transicao2.Trigger);
                estado = transicao2.Destination;
            }

            // executa os eventos não controlaveis q ainda não forma executados
            while (schAV.Select(ind => !ind.Key.IsControllable && !float.IsInfinity(ind.Value)).Any(s => s))
            {
                var tmin = transitions[estado].Where(t => !t.IsControllableTransition ).Select(t => schAV[t.Trigger]).Min();
                var transicao1 = transitions[estado].First(t => !t.IsControllableTransition && schAV[t.Trigger] == tmin);

                tempo += schAV[transicao1.Trigger];
                
                schAV = update(schAV, transicao1.Trigger);
                seqAval.Add(transicao1.Trigger);
                estado = transicao1.Destination;
            }

            if (estado != inicial) tempo = 1234; //throw new Exception("A busca deve chegar a um estado marcado"); //

            //var pcSeq = pcPreserveSeqAVL;
            return (tempo, seqAval.ToArray(), newDvstate.ToArray());
        }

        // GU: Modificação  doa TimeEvaluation para tbm salvar os estados divergente
        private static (double time, AbstractEvent[] sequency, AbstractState[] dvstate) TimeDivStatesEvaluation(
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
            var newDvstate = new List<AbstractState>();

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
                    // armazena os estados divergentes
                    if (trans.Count() > 1 && trans.Where(tr => tr.IsControllableTransition).Count() > 1 && e.IsControllable == true )
                    {
                        newDvstate.Add(state);
                    } 
                    // atualiza os parâmetros
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

            //return state == destination ? time : float.PositiveInfinity;
            return (time, sequence, newDvstate.ToArray());
        }

        private static IEnumerable<AbstractEvent> GreedyTime(
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


        private static IEnumerable<AbstractEvent> GreedyParallelism(
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
        private static float TimeEvaluation(
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
        private static float TimeEvaluationControllable(
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


        private static float ParallelismEvaluation(
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


        private static IEnumerable<AbstractEvent> HeuristicShortestMakespan(
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


        private static IEnumerable<AbstractEvent> LogicalMaximumParallelism(
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

            IDictionary<AbstractState,Tuple<uint, SinglyLinkedList<AbstractEvent>,Restriction>>
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


        private static IEnumerable<AbstractEvent> TimedMaximumParallelism(
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
                         alias % 2 == 0 ? Controllability.Uncontrollable : Controllability.Controllable));

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

                Supervisor = DFA.MonolithicSupervisor(new[] { c1, c2, fresa, torno, robot, mm, c3, mp },
                    new[] { e1, e2, e3, e4, e5, e6, e7, e8 }, true);

                Utilidades.SerializeAutomaton(Supervisor, "SFM.bin");
            }
        }

        public DFA Supervisor { get; }

        public DFA Seq_producao { get; }

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
                    //sch[_e[65]] = 0;        // modificação gustavo.
                    break;
                case "65":
                    sch[_e[66]] = 25;
                    //sch[_e[63]] = 0;        // modificação gustavo
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
            var s = new[] {
                new ExpandedState("0", 0, Marking.Marked),
                new ExpandedState("1", 1, Marking.Unmarked),
                new ExpandedState("2", 2, Marking.Unmarked)
            };

            _e = new[] { 1, 2, 3, 4, 5, 6, 7, 8}.ToDictionary(alias => alias,
                alias => new Event(alias.ToString(),
                      alias % 2 == 0 ? Controllability.Uncontrollable : Controllability.Controllable)
                      );

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

            s = new[] {
                new ExpandedState("E",  0, Marking.Marked),
                new ExpandedState("F",  1, Marking.Unmarked)                
            };

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
                    new Transition(s[0], _e[4], s[1]),
                    new Transition(s[1], _e[5], s[0])
                },
                s[0], "E2");

            var e3 = new DeterministicFiniteAutomaton(
               new[]
               {
                    new Transition(s[0], _e[6], s[1]),
                    new Transition(s[1], _e[7], s[0])
               },
               s[0], "E3");

            Supervisor = DFA.MonolithicSupervisor(
                new[] { m1, m2, m3, m4},
                new[] { e1, e2, e3 },
                true);

            s = new[] {
                new ExpandedState("3",  0, Marking.Marked),
                new ExpandedState("1",  1, Marking.Unmarked),
                new ExpandedState("2",  2, Marking.Unmarked)
            };

            Seq_producao = new DeterministicFiniteAutomaton(new []
            {
                 new Transition(s[1], _e[7], s[2]),
                 new Transition(s[2], _e[7], s[0])
            },
            s[1],"Seq");
        }

        public int Depth => 8;

        public Scheduler InitialScheduler =>
            _e.ToDictionary(kvp => kvp.Value as AbstractEvent,
                kvp => kvp.Value.IsControllable ? 0.0f : float.PositiveInfinity);

        public AbstractState InitialState => Supervisor.InitialState;

        public DFA Supervisor { get; }

        public DFA Seq_producao { get; }

        public AbstractState TargetState => Supervisor.InitialState;

        public Update UpdateFunction => (old, ev) =>
        {
            // atualizando com base no evento ocorrido
            var sch = old.ToDictionary(kvp => kvp.Key, kvp =>
            {
                if (kvp.Key.IsControllable) return 0;

                var v = kvp.Value - old[ev];

                return v < 0 ? float.PositiveInfinity : v;
            });
            // caso o evento não seja controlável
            if (!ev.IsControllable) sch[ev] = float.PositiveInfinity;
            // se for controlável
            switch (ev.ToString())
            {
                case "1":
                    sch[_e[2]] = 25;
                    break;
                case "3":
                    sch[_e[4]] = 25;
                    break;
                case "5":
                    sch[_e[6]] = 25;
                    break;
                case "7":
                    sch[_e[8]] = 15;
                    break;
            }
            return sch;
        };

        public Restriction InitialRestrition(int products)
        {
            return new Restriction
            {
                {_e[1], (uint) (1*products)},
                {_e[3], (uint) (1*products)},
                {_e[5], (uint) (1*products)},
                {_e[7], (uint) (1*products)}
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

                var s = new[] { new ExpandedState("0", 0, Marking.Marked), new ExpandedState("1", 1, Marking.Unmarked) };



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

                Supervisor = DFA.MonolithicSupervisor(new[] { m1, m2, m3, m4, m5, m6 },
                    new[] { e1, e2, e3, e4 }, true);

                Utilidades.SerializeAutomaton(Supervisor, "ITL.bin");
            }
        }

        public int Depth => 12;

        public Scheduler InitialScheduler =>
            _e.ToDictionary(kvp => kvp.Value as AbstractEvent,
                kvp => kvp.Value.IsControllable ? 0.0f : float.PositiveInfinity);

        public AbstractState InitialState => Supervisor.InitialState;

        public DFA Supervisor { get; }

        public DFA Seq_producao { get; }

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
            Stream stream = new FileStream(
                path,
                FileMode.Create,
                FileAccess.Write,
                FileShare.None
                );
            formatter.Serialize(stream, G);
            stream.Close();
        }

        public static DFA DeserializeAutomaton(string path)
        {
            IFormatter formatter = new BinaryFormatter();
            Stream stream = new FileStream(
                path,
                FileMode.Open,
                FileAccess.Read,
                FileShare.Read
                );
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

    public class MyRandom : Random
    {
        public MyRandom()
        {
        }

        public MyRandom(int Seed) : base(Seed)
        {
        }

        public override double NextDouble()
        {
            lock (this)
            {
                return base.NextDouble();
            }
        }

        public override int Next()
        {
            lock (this)
            {
                return base.Next();
            }
        }

        public override int Next(int i)
        {
            lock (this)
            {
                return base.Next(i);
            }
        }

        public override int Next(int i, int j)
        {
            lock (this)
            {
                return base.Next(i, j);
            }
        }
    }
}

/*
  var transicoes = sp
          .Transitions.AsParallel()
          .GroupBy(t => t.Origin)
          .ToDictionary(gr => gr.Key, gr => gr.ToArray());

  var ss =
       Enumerable.Range(0, 9)
           .Select(i =>
               new State(i.ToString(),
                   i == 0
                       ? Marking.Marked
                       : Marking.Unmarked)
           ).ToArray();

  var dist_state = 2 + 1; // num_event_dist + 1
  var bfs_paths = BFS_path_finder(ss[4], ss[7], dist_state, transicoes);

  print_bfs(bfs_paths);  // retorna os resultados
  */
