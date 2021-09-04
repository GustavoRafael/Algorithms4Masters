
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
using sequencia_projecao_v10;


namespace sequencia_projecao_v10
{
	internal class Program
	{
		const int limiar = 100;

		private static readonly MyRandom Rnd = new MyRandom();

		private static void Main()
		{
			System.Threading.Thread.CurrentThread.Priority = System.Threading.ThreadPriority.AboveNormal;

            // Inicialização do ClusterTool 
            int layout = 1, tempocamaras = 10, numcamaras = 4;
            var problem = new CTESsep(layout, tempocamaras, numcamaras);                             
            
            
			// Inicialização dos outros problemas (SF, SFM, ITL)
			//var problem = new SFM();

            // quantidade de produtos no lote
            //int[] numProducts = Enumerable.Range(1,8).ToArray(); // 1 ate 10
            int[] numProducts = { 1, 2, 4}; //, 100, 500, 1000, 1500};
			//int[] numProducts = { 6, 12, 25, 50, 100 };

			// execução dos métodos de otimização
			foreach (var nProd in numProducts)
			{
                // algoritmo maximo paralelismo
                Max_Paralelismo_algoritmo(problem, nProd);
                // algoritmo clonal
                Clonal_algoritmo(problem, nProd);
                // nova linha
				Console.WriteLine("\n");
			}                      

            // fim, mantem o terminal aberto.
            Console.Read();
		}

		private static double SequenceCount(DeterministicFiniteAutomaton g)
		{
			
			var ms = g.MarkedStates.ToArray();                                      //gets the marked states of g
            
            if (ms.Count() > 1) { return 0; }                                       //if there is more than 1 marked states, ends the function     

            var tr = g.Transitions.ToList();                                        //gets a list with all transictions of g

            List<Transition> transitions_to_remove = new List<Transition>();        //creates a list that stores transictions to be removed from tr            
            List<AbstractState> state_destination = new List<AbstractState>();      //creates a list that stores destination states for the transictions            
            List<AbstractState> state_origin = new List<AbstractState>();           //creates a list that stores origin states for the transictions

            
            state_destination.Add(ms[0]);                                           //adds the marked state to the state destination list... 
                                                                                    // ... The algorithm starts with the marked state
            
            var maxNumPosSeq = 30000;                                               //creates a vector that stores the number of possible sequences from a state ...
                                                                                    //...that has the same index in destination state list
            var sequences = Enumerable.Range(0, maxNumPosSeq).Select(j => 0.0).ToArray();
			var acumulated = Enumerable.Range(0, maxNumPosSeq).Select(i => 0.0).ToArray();

			int num_estados = 1;                                                    //number of states in the first level, the marked state
			bool marked = true;

			//while there is transitions in the list
			while (tr.Count() > 0)
			{
				int aux = 0;                                                        //number of transitions that have origin in the next level
				//for each state in the level
				for (int j = 0; j < num_estados; j++)
				{
					//for each transition in the transition list
					foreach (var t in tr)
					{
						//if the transition destination is equal to state j in the level being analyzed
						if (t.Destination == state_destination.ElementAt(j))
						{
							//if the state j is marked
							if (marked)
							{
								state_origin.Add(t.Origin);                     //add the state origin of transition t in the origin states list 
								sequences[aux] = 1;                             //number of paths from marked state to origin state of t 
								aux++;                                          //increment number of transitions that have origin in the next level
								transitions_to_remove.Add(t);                   //add t in the list of transitions to be removed
								marked = false;
							}
							else
							{
								state_origin.Add(t.Origin);                     //add the state origin of transition t in the origin states list 
								sequences[aux] = acumulated[j];                 //number of paths from marked state to origin state of t through state j
								aux++;                                          //increment number of transitions that have origin in the next level
								transitions_to_remove.Add(t);                   //add t in the list of transitions to be removed
							}
						}
					}

					//for each transition in the list of the transitions to be removed
					foreach (var u in transitions_to_remove)
					{
						tr.Remove(u);                                           //removes it from the transition list
					}
					transitions_to_remove.Clear();                              //clears the transitions to be removed list
				}
            
				var sequences_aux = Enumerable.Range(0, maxNumPosSeq).Select(i => 0.0).ToArray();

				List<AbstractState> estado_sem_dupli = state_origin.Distinct().ToList(); //gets only one occurence of each state in the origin state list

				//for each state in the list of origin states without duplicates
				for (int m = 0; m < estado_sem_dupli.Count(); m++)
				{
					//gets the indexes from the origin state list where the state is equal to the state m
					var result = Enumerable.Range(0, state_origin.Count).Where(i => state_origin[i] == estado_sem_dupli.ElementAt(m)).ToList();

					//for each occurence of the state m in the origin state list
					for (int k = 0; k < result.Count(); k++)
					{
						sequences_aux[m] += sequences[result.ElementAt(k)];     //adds the number of paths from marked state to 
																				//state m through diferent transitions which have origin in the state m
					}
				}

				state_origin = estado_sem_dupli.ToList();                       // updates the origin state list
				estado_sem_dupli.Clear();                                       //clears the list of inique occurence of states
				sequences = sequences_aux;                                      //updates the vector of sequences
				state_destination = state_origin.ToList();                      //updates the state destination list, now the next level becomes the current level

				//for each state in the origin state list
				for (int i = 0; i < state_origin.Count; i++)
				{
					acumulated[i] = sequences[i];                               //updates the number of paths from marked state to state i
				}

				num_estados = state_origin.Count;                               //gets the number of states in the current level
				state_origin.Clear();                                           //clears the state origin list
			}
			return sequences[0];                                                //returns the number of paths from marked state to inicial state
		}

		private static void NumSequencesAbstraction(ISchedulingProblem plant)
		{
			// Problemas teste: SFM, SF, ITL e Cluster Tool
			plant.Supervisor.simplifyName();
            Console.WriteLine("Supervisor produto: {0} estados e {1} transições", plant.Supervisor.States.Count(), plant.Supervisor.Transitions.Count());

            var proj1 = plant.Supervisor.Projection(plant.Supervisor.UncontrollableEvents).Trim;
            Console.WriteLine("Projeção do supervisor: {0} estados e {1} transições", proj1.States.Count(), proj1.Transitions.Count());


            // lista com tres sequencias de produção de teste
            var seqProduction = new[] { plant.Seq_producaoC }.ToList();//plant.Seq_producaoA, plant.Seq_producaoB, plant.Seq_producaoC }.ToList();

			// Calcula o numero de soluções para cada problema, com abstração e com o supervisor.
			foreach (var sprod in seqProduction)
			{
				// Problema Com o supervisor
				var seqsFromSupervisor = DeterministicFiniteAutomaton.ParallelComposition(plant.Supervisor, sprod).Trim;
				seqsFromSupervisor.simplifyName();

				Console.WriteLine("Supervisor Produto: {0} estados e {1} transições",seqsFromSupervisor.States.Count(), seqsFromSupervisor.Transitions.Count());
				//Console.WriteLine($"Numero de soluções factiveis no supervisor:{ SequenceCount(seqsFromSupervisor)}");
                
				// Processo de criação da abstração do supervisor.
				// Projeção nos controláveis
				var proj = plant.Supervisor.Projection(plant.Supervisor.UncontrollableEvents);
				//Console.WriteLine("Projeção do supervisor: {0} estados e {1} transições", proj.States.Count(), proj.Transitions.Count());

				// trim e simplificar o nome dos estados
				var seqFromAbstraction = DeterministicFiniteAutomaton.ParallelComposition(proj, sprod).Trim;
				seqFromAbstraction.simplifyName();

				Console.WriteLine("Abstração pos trim: {0} estados e {1} transições",seqFromAbstraction.States.Count(), seqFromAbstraction.Transitions.Count());
                //Console.WriteLine($"Numero de soluções factiveis Abstração:{SequenceCount(seqFromAbstraction)}");
			}
		}

		private static void Max_Paralelismo_algoritmo(ISchedulingProblem plant, int nprod)              // Alg. do Lucas (TMP, HSM, LMP) 
		{
			sequencia_projecao_v10.ClassMXP mxp = new ClassMXP();
			sequencia_projecao_v10.CLONALClass cMet = new CLONALClass();

			System.Threading.Thread.CurrentThread.Priority = System.Threading.ThreadPriority.AboveNormal;
			System.Threading.Thread.CurrentThread.CurrentCulture = new System.Globalization.CultureInfo("en-US");

			float maxIt = 30; //5;

			// inicializando parâmetros do cluster tool 
			//var layout = 1;
			//var tempocamaras = 200;
			//int numcamaras = 4;
			//ISchedulingProblem plant = new CTESsep(layout, tempocamaras, numcamaras);          // para os testes do cluster tool

			//ISchedulingProblem plant = new SF();

			var transitions = plant.Supervisor
				.Transitions.AsParallel()
				.GroupBy(t => t.Origin)
				.ToDictionary(gr => gr.Key, gr => gr.ToArray());

			Func<int, AbstractEvent[]>[] tests = new Func<int, AbstractEvent[]>[1];

			tests[0] = (prod) => mxp.TimedMaximumParallelism(
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
            tests[2] = (prod) => mxp.HeuristicShortestMakespan(
                    plant.Supervisor,
                    plant.InitialState,
                    plant.TargetState,
                    plant.Depth * prod,
                    plant.InitialScheduler,
                    plant.UpdateFunction,
                    plant.InitialRestrition(prod),
                    transitions
                    ).ToArray();
            tests[3] = (prod) => mxp.GreedyTime(
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

			//Console.WriteLine("Configurações terminadas\nSupervisor com {0} estados e {1} transições",
			//  plant.Supervisor.States.Count(),
			//plant.Supervisor.Transitions.Count()
			//);
			int count = 0;

			// realização dos teste acima simplificado
			bool testes2_0n = true; // controla a habilitação do teste abaixo
									//bool testes2_0ff = false; // controla a habilitação do teste abaixo
			if (testes2_0n)
			{
				foreach (var test in tests)
				{
					Console.WriteLine("\n-------------------------------------\n");

					foreach (var products in new[] { nprod })// 1,2,3,4,5,6,7,8,9,10 })//1, 5, 10, 50, 100, 500, 1000 })
					{
						var lst = new List<AbstractEvent[]>();
						Stopwatch timer = new Stopwatch();
						timer.Start();
						for (var it = 0; it < maxIt; it++)                      // maxIt: numero de vezes que uma sequencia é gerada
							lst.Add(test(products));
						timer.Stop();

						var divStates = cMet.TimeDivStatesEvaluation(
							plant.Supervisor,
							plant.InitialState,
							plant.TargetState,
							lst.First().ToArray(),                              // sequencia 
							plant.InitialScheduler,
							plant.UpdateFunction,
							plant.InitialRestrition(products),
							transitions
							);

						var makespan = lst.Select(s => time(products, s)).Average();
						var parallelism = lst.Select(s => paralell(products, s)).Average();
						float optimizationTime = timer.ElapsedMilliseconds / maxIt;            // tempo em minutos
						var seqSize = lst.ToArray()[0].Count();
						var numDvStates = divStates.dvstate.Count();
                        /*
						Console.Write("{{{0}, tempo(ms):{1}, {2}, {3}, {4}, {5}}}, \n ",
							products,
							Math.Round(optimizationTime, 6),
							//optimizationTime,
							float.IsNaN(makespan) ? -1.0f : makespan,
							parallelism,
							seqSize,
							numDvStates);*/
                        Console.WriteLine($"prod:{products}, time(ms):{Math.Round(optimizationTime, 6)}, mks:{ makespan}, parall:{parallelism}," +
                            $" seqSize:{seqSize}, numDS:{numDvStates}");
					}
					count = count + 1;
				}
			}
			//ReadFileSeqTimed(plant, transitions,"lucasSeq.txt",8);                // imprime o tempo de uma seq de um arquivo
		}

		private static void Clonal_algoritmo(ISchedulingProblem plant1, int numProdA)                   // Método de otmização Clonal    
		{
			System.Threading.Thread.CurrentThread.Priority = System.Threading.ThreadPriority.AboveNormal;
			System.Threading.Thread.CurrentThread.CurrentCulture = new System.Globalization.CultureInfo("en-US");

            // chamada do algoritmo clonal e outras ferramentas
			sequencia_projecao_v10.CLONALClass mtClonal = new CLONALClass();
			sequencia_projecao_v10.ToolsClass tools = new ToolsClass();

			//ISchedulingProblem plant1 = new SF();                                 // para testes do SFM, SF e ITL
			//plant1.Supervisor.simplifyName();
			//var p1 = plant1.Supervisor.Trim;
			var transitions1 = plant1.Supervisor
				.Transitions.AsParallel()
				.GroupBy(t => t.Origin)
				.ToDictionary(gr => gr.Key, gr => gr.ToArray());

			// Parâmetros do algoritmo
			var pbtState = 1.0;                                                     // probabilidade de troca aleatéoria nos estados divergentes
            int indPolulacao = 10; //(prods 1-11, 25),100                            / 25 - Número de indivíduos inicial(População)
			int numIndividuosMutados = 5; //15 -20                                  // 15 - Número de indivíduos máximo.
			int maxGeracoes = 20;                                                   // 40 - numero máximo de gerações 
			int indSelecGeracao = 1;                                                //  2 - Número de indivíduos selecionados a cada nova geração.
			int GeracaoSemMelhorasMax = 5;                                          //  5 - Número máximo de gerações sem melhoras
			int numMaxRept = 10;                                                    // Número de máximo de repetições do algoritimo clonal


			// Parâmetros para repetições
			string[] src = { "randInd" }; // "randInd", "mixRandMfe","TMP", "HSM", "mixRandTMP", "mixRandHSM", "LMP", "mixRandLMP" };         // Métodos de Geração dos Indivíduos.

            double mixPercentual = 0.15 ; //, 
            int[] numProd = { numProdA };
            double percentual_DS_preserved = 0.85; 

            // variaveis de armazenamento
            AbstractEvent[][] bestSeq = new AbstractEvent[][] { };
            double[] bestMsp = { 15000.0 };

            var data = new List<(double time, int iter, double medMakespam, int nGeracoes, int dsCount, int seqSizes)>();
			var dataSave = new List<(double numProdc, string source, double time, double iter, double nGeracoes, double MakespamMin, double MakespamMed, double MakespamSTD, double MakespamMAX)>();
            var storeData = new List<double>();

            //Console.Write($"\n\n  -- NumProdutos: A = B = {prodA} --\n");
            //Console.Write($"\n Metodo: {sc}\n");
            //Console.Write($" TimeMedOtm (s/exe),  NumMedIter , NumMedGer, Makespam min, Makespam medio, Makespam Max, PropMistura \n");
            //Console.Write($"\n\n num prod, source, TimeMedOtm (min),  NumMedIter , NumMedGer, Makespam min, Makespam medio, MakespamSTD, Makespam Max \n");

            // Teste parametros
            var maxtestValue = 1;
            var testedValue = Enumerable.Range(1, maxtestValue).ToArray(); //new double[] { 0.99, 0.99, 0.97, 0.96, 0.95, 0.94, 0.9, 0.85, 0.8, 0.75, 0.7, 0.65, 0.6, 0.55, 0.5, 0.45, 0.35, 0.3, 0.25, 0.2, 0.15, 0.10 }; // 


            var timerTotal = new Stopwatch();                                       // tempo total
			timerTotal.Start();
			foreach (var testvar in testedValue) //testvar, /// (sob teste) 
            {
				foreach (var sc in src)
				{
					//Console.Write($"\n\n Metodo: {sc}\n");
					data.Clear();
					for (int rept = 0; rept < numMaxRept; rept++)           // escopo do metodo clonal 
					{
						var timer1 = new Stopwatch();
						timer1.Start();

						var result = mtClonal.CLONAL(
							plant1,
                            numProdA, //prodA,
							transitions1,
							pbtState,
                            indPolulacao,
                            numIndividuosMutados,
                            maxGeracoes,
                            indSelecGeracao,
                            GeracaoSemMelhorasMax,
							sc,                                         // source of individuals for the optimization
                            mixPercentual,
                            percentual_DS_preserved
                            );

						timer1.Stop();
						//Console.Write($"\n Otimização finalizada em {timer1.ElapsedMilliseconds} mili-segundos. \n");
						var medMakespam = result.Item1.Select(idt => idt.time).Min();
						var medMakespam1 = result.Item1.Select(idt => idt.time).Average();
						var seqTam = result.Item1.Where(sw => sw.time == medMakespam).Select(stw => stw.sequency).ToArray()[0].Count();
                        var dsStatesCount = result.Item1.Where(sw => sw.time == medMakespam).Select(info => info.dvState).ToArray()[0].Count();

                        
						if (medMakespam <= bestMsp.Min())
						{
							bestMsp = result.Item1.Where(sw => sw.time == medMakespam).Select(stw => stw.time).ToArray();
							bestSeq = result.Item1.Where(sw => sw.time == medMakespam).Select(stw => stw.sequency).ToArray();

                            // salva a melhor sequencia
                            //tools.WriteFileSeqTimed(bestMsp, bestSeq, "result"+ rept.ToString()+ "_" + np.ToString() + "_ITL_bestSeq.txt");
                        }

						// prints antigos por execução
						var numGeracoes = result.numeroTotalGeracoes;
						data.Add((timer1.ElapsedMilliseconds, result.numAvalfobj, medMakespam, numGeracoes, dsStatesCount, seqTam));
                        
                        // inicio - Console.Write($"\n Avaliação {rept + 1}/{numMaxRept}, mks: {medMakespam}, tempo Lucas {tl}, paralelismo {Math.Round(parall, 0)}, num divSates {divStatesChecking.dvstate.Count()},numGeracoes {numGeracoes}, Tamanho da sequencia {seqTam},tempo (ms): {timer1.ElapsedMilliseconds}");
						//ultimo - 
						//Console.Write($"\n Avaliação {rept + 1}/{numMaxRept}, mks: {medMakespam}, {medMakespam1} ,numGeracoes {numGeracoes}, tempo (ms): {timer1.ElapsedMilliseconds}, tam:{seqTam}");
					}

                    Console.Write($"\n TimeMedOtm (ms/exe): {data.Select(ck => ck.time).Average()},  NumMedAval.FO. {data.Select(ni => ni.iter).Average()}," + $" NumMedGer {data.Select(ng => ng.nGeracoes).Average()}");
                    //Console.Write($"\n Makespam min {data.Select(mk => mk.medMakespam).Min()}, " +  $"Makespam medio {Math.Round(data.Select(mk => mk.medMakespam).Average(), 2)}, Makespam Max {data.Select(mk => mk.medMakespam).Max()}\n");
                    var dscc = data.Where(mks => mks.medMakespam == data.Select(mk => mk.medMakespam).Min()).Select(mk => mk.dsCount).Max();

                    Console.Write($"\n\n {(testvar)},  {numProdA}, {sc}, tempo (min):{Math.Round((data.Select(ck => ck.time).Sum()) / (60000), 3)}, {Math.Round(data.Select(ni => ni.iter).Average(), 2)}, {Math.Round(data.Select(ng => ng.nGeracoes).Average(), 2)},");
					Console.Write($" {data.Select(mk => mk.medMakespam).Min()}, {Math.Round(data.Select(mk => mk.medMakespam).Average(), 2)}, " +
						$" {Math.Round((data.Select(mk => mk.medMakespam).ToList()).StandardDeviation(), 2)}, {data.Select(mk => mk.medMakespam).Max()}" +
                         $" , num DS States: {dscc}, seqSize:{data.Where(mks => mks.medMakespam == data.Select(mk => mk.medMakespam).Min()).Select(stw => stw.seqSizes).First()} \n"); //, {mp}\n");

                    
                    // salvar os valores de uma variável apos N runs
                    //storeData.Add(Math.Round(data.Select(mk => mk.medMakespam).Average(), 2));                   
                    //tools.SaveData(data.Select(info=> info.medMakespam).ToList(),"SFM_5P_" + (mixPercentual * 100).ToString() + "_" + src.First());   
                }
                /*
                dataSave.Add((
                        (testvar),
                        src.First(),
                        Math.Round((data.Select(ck => ck.time).Sum()) / 60000, 3),
                        Math.Round(data.Select(ni => ni.iter).Average(), 2),
                        Math.Round(data.Select(ng => ng.nGeracoes).Average(), 2),
                        data.Select(mk => mk.medMakespam).Min(),
                        Math.Round(data.Select(mk => mk.medMakespam).Average(), 2),
                        Math.Round((data.Select(mk => mk.medMakespam).ToList()).StandardDeviation(), 2),
                        data.Select(mk => mk.medMakespam).Max()
                        )); 
                */
            }
            // salva cara resultado num arquivo
            //tools.WriteDataFile2(dataSave, "z_sfm_1010_Mutation Rate_02"); //data colection
            
            // salvar os valores dos experimentos
            //tools.SaveDataOf2Variable(testedValue.ToList(), storeData, "T08_mixRandTMAvgMsp");


            timerTotal.Stop();
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
				63, 65, 64, 66, 71, 72, 73, 74, 81, 82,93,95
			}.ToDictionary(alias => alias,
				 alias => new Event(alias.ToString(), alias % 2 == 0 ? Controllability.Uncontrollable : Controllability.Controllable));

			System.Threading.Thread.CurrentThread.CurrentCulture = new System.Globalization.CultureInfo("en-US");
			String directory = @"C:\Users\GustavoCaetano\Dropbox\2018_S01\CBA_2018\code_v5\USER\";

			if (File.Exists(directory + "SFM2.bin"))
			{
				Supervisor = Utilidades.DeserializeAutomaton(directory + "SFM2.bin");

				var s = new[]
				{
					new ExpandedState("0",  0, Marking.Marked),
					new ExpandedState("1",  1, Marking.Unmarked),
					new ExpandedState("2",  2, Marking.Unmarked),
					new ExpandedState("3",  3, Marking.Unmarked),
					new ExpandedState("4",  4, Marking.Unmarked),
					new ExpandedState("5",  5, Marking.Unmarked),
					new ExpandedState("6",  6, Marking.Unmarked),
					new ExpandedState("7",  7, Marking.Unmarked),
					new ExpandedState("8",  8, Marking.Unmarked),
					new ExpandedState("9",  9, Marking.Unmarked)
			   };

				Seq_producaoA = new DeterministicFiniteAutomaton(new[]
				{
					new Transition(s[1], _e[63], s[2]),
					new Transition(s[2], _e[65], s[0]),
					new Transition(s[1], _e[65], s[3]),
					new Transition(s[3], _e[63], s[0])
				}, s[1], "SeqA");

				Seq_producaoB = new DeterministicFiniteAutomaton(new[]
			   {
				 new Transition(s[1], _e[65], s[2]),
				 new Transition(s[2], _e[65], s[3]),
				 new Transition(s[3], _e[63], s[4]),
				 new Transition(s[4], _e[63], s[0]),
				 new Transition(s[1], _e[63], s[5]),
				 new Transition(s[5], _e[63], s[6]),
				 new Transition(s[6], _e[65], s[7]),
				 new Transition(s[7], _e[65], s[0]),
				 new Transition(s[5], _e[65], s[8]),
				 new Transition(s[2], _e[63], s[8]),
				 new Transition(s[8], _e[65], s[4]),
				 new Transition(s[8], _e[63], s[7])
				}, s[1], "SeqB");

			}
			else
			{

				var s = Enumerable.Range(0, 20)
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

				s = Enumerable.Range(0, 20)
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


				Seq_producaoA = new DeterministicFiniteAutomaton(new[]
				{
					new Transition(s[1], _e[63], s[2]),
					new Transition(s[2], _e[65], s[0]),
					new Transition(s[1], _e[65], s[3]),
					new Transition(s[3], _e[63], s[0])
				}, s[1], "SeqA");

				Seq_producaoB = new DeterministicFiniteAutomaton(new[]
				{
					new Transition(s[1], _e[65], s[2]),
					new Transition(s[2], _e[65], s[3]),
					new Transition(s[3], _e[63], s[4]),
					new Transition(s[4], _e[63], s[0]),
					new Transition(s[1], _e[63], s[5]),
					new Transition(s[5], _e[63], s[6]),
					new Transition(s[6], _e[65], s[7]),
					new Transition(s[7], _e[65], s[0]),
					new Transition(s[5], _e[65], s[8]),
					new Transition(s[2], _e[63], s[8]),
					new Transition(s[8], _e[65], s[4]),
					new Transition(s[8], _e[63], s[7])
				}, s[1], "SeqB");

				Seq_producaoC = new DeterministicFiniteAutomaton(new[]
				{
					new Transition(s[1], _e[63], s[2]),
					new Transition(s[2], _e[63], s[3]),
					new Transition(s[3], _e[63], s[4]),
					new Transition(s[4], _e[65], s[8]),
					new Transition(s[8], _e[65], s[12]),
					new Transition(s[12], _e[65], s[0]),
					new Transition(s[1], _e[65], s[5]),
					new Transition(s[5], _e[65], s[9]),
					new Transition(s[9], _e[65], s[13]),
					new Transition(s[13], _e[63], s[14]),
					new Transition(s[14], _e[63], s[15]),
					new Transition(s[15], _e[63], s[0]),
					new Transition(s[2], _e[65], s[6]),
					new Transition(s[6], _e[65], s[10]),
					new Transition(s[10], _e[65], s[14]),
					new Transition(s[3], _e[65], s[7]),
					new Transition(s[7], _e[65], s[11]),
					new Transition(s[11], _e[65], s[15]),
					new Transition(s[5], _e[63], s[6]),
					new Transition(s[6], _e[63], s[7]),
					new Transition(s[7], _e[63], s[8]),
					new Transition(s[9], _e[63], s[10]),
					new Transition(s[10], _e[63], s[11]),
					new Transition(s[11], _e[63], s[12])
				},
				s[1], "SeqC");
			}
		}

		public DFA Supervisor { get; }

		public DFA Seq_producaoA { get; }

		public DFA Seq_producaoB { get; }

		public DFA Seq_producaoC { get; }

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

			switch (ev.ToString())  // se os valores de tempo não permitirem q o codigo compile, diminuir eles em uma unidade (valor - 1)
			{
				case "11":
					sch[_e[12]] = 26-1;
					break;
				case "21":
					sch[_e[22]] = 26 - 1;
					break;
				case "31":
					sch[_e[32]] = 22 - 1;
					break;
				case "33":
					sch[_e[34]] = 20 - 1;
					break;
				case "35":
					sch[_e[36]] = 17 - 1;
					break;
				case "37":
					sch[_e[38]] = 25 - 1;
					break;
				case "39":
					sch[_e[30]] = 21 - 1;
					break;
				case "41":
					sch[_e[42]] = 31 - 1;
					break;
				case "51":
					sch[_e[52]] = 39 - 1;
					break;
				case "53":
					sch[_e[54]] = 33 - 1;
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
					sch[_e[72]] = 26 - 1;
					break;
				case "73":
					sch[_e[74]] = 26 - 1;
					break;
				case "81":
					sch[_e[82]] = 25 - 1;
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

			_e = new[] { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 }.ToDictionary(alias => alias,
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
            
			var e4 = new DeterministicFiniteAutomaton(
			   new[]
			   {
					new Transition(s[0], _e[8], s[1]),
					new Transition(s[1], _e[9], s[0])
			   },
			   s[0], "E4");

            var e5 = new DeterministicFiniteAutomaton(
               new[]
               {
                    new Transition(s[0], _e[10], s[1]),
                    new Transition(s[1], _e[11], s[0])
               },
               s[0], "E5");

            Supervisor = DFA.MonolithicSupervisor(
				new[] { m1, m2, m3, m4, m5, m6 },
				new[] { e1, e2, e3, e4, e5 },
				true);
            /*
            Supervisor = DFA.MonolithicSupervisor(
                new[] { m1, m2, m3, m4 },
                new[] { e1, e2, e3 },
                true);
            */

            s = Enumerable.Range(0, 10)
					.Select(i =>
						new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked))
					.ToArray();

			Seq_producaoA = new DeterministicFiniteAutomaton(new[]
			{
				new Transition(s[1], _e[7], s[2]),
				new Transition(s[2], _e[7], s[0])
				//new Transition(s[3], _e[9], s[4]),
				//new Transition(s[4], _e[9], s[0])
                //new Transition(s[5], _e[7], s[6]),
                //new Transition(s[6], _e[7], s[0])
            }, s[1], "SeqA");

			Seq_producaoB = new DeterministicFiniteAutomaton(new[]
			{
				new Transition(s[1], _e[9], s[2]),
				new Transition(s[2], _e[9], s[3]),
				new Transition(s[3], _e[9], s[4]),
				new Transition(s[4], _e[9], s[5]),
				new Transition(s[5], _e[9], s[0])
                //new Transition(s[6], _e[7], s[0])
            }, s[1], "SeqB");

			Seq_producaoC = new DeterministicFiniteAutomaton(new[]
			{
				new Transition(s[1], _e[1], s[2]),
				new Transition(s[2], _e[3], s[3]),
				new Transition(s[3], _e[1], s[4]),
				new Transition(s[4], _e[5], s[5]),
                new Transition(s[5], _e[3], s[6]),
                new Transition(s[6], _e[7], s[7]),
				new Transition(s[7], _e[5], s[8]),
                new Transition(s[8], _e[7], s[0])
            }, s[1], "SeqC");
            /*
            Seq_producaoC = new DeterministicFiniteAutomaton(new[]
            {
                new Transition(s[1], _e[9], s[2]),
                new Transition(s[2], _e[9], s[3]),
                new Transition(s[3], _e[9], s[4]),
                new Transition(s[4], _e[9], s[5]),
                new Transition(s[5], _e[9], s[6]),
                new Transition(s[6], _e[9], s[0])
            }, s[1], "SeqC");
            */
        }

		public int Depth => 12;  // para 4 maquinas é 8, 6 maquinas 12

		public Scheduler InitialScheduler =>
			_e.ToDictionary(kvp => kvp.Value as AbstractEvent,
				kvp => kvp.Value.IsControllable ? 0.0f : float.PositiveInfinity);

		public AbstractState InitialState => Supervisor.InitialState;

		public DFA Supervisor { get; }

		public DFA Seq_producaoA { get; }

		public DFA Seq_producaoB { get; }

		public DFA Seq_producaoC { get; }

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
					sch[_e[2]] = 12;
					break;
				case "3":
					sch[_e[4]] = 12;
					break;
				case "5":
					sch[_e[6]] = 12;
					break;
				case "7":
					sch[_e[8]] = 12;
					break;
				case "9":
					sch[_e[10]] = 12;
					break;
                case "11":
                    sch[_e[12]] = 12;
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
				{_e[7], (uint) (1*products)},
				{_e[9], (uint) (1*products)},
                {_e[11], (uint) (1*products)}
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

			if (File.Exists("ITL1.bin"))
			{
				Supervisor = Utilidades.DeserializeAutomaton("ITL1.bin");
				/*var s = new[]
                {
                    new ExpandedState("0",  0, Marking.Marked),
                    new ExpandedState("1",  1, Marking.Unmarked),
                    new ExpandedState("2",  2, Marking.Unmarked),
                    new ExpandedState("3",  3, Marking.Unmarked),
                    new ExpandedState("4",  4, Marking.Unmarked)
                    //new ExpandedState("5",  5, Marking.Unmarked),
                    // new ExpandedState("6",  6, Marking.Unmarked)
                };
                */

				var s = Enumerable.Range(0, 8)
					.Select(i =>
						new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked))
					.ToArray();

				Seq_producaoA = new DeterministicFiniteAutomaton(new[]
				{
					new Transition(s[1], _e[11], s[2]),
					new Transition(s[2], _e[11], s[3]),
					new Transition(s[3], _e[11], s[4]),
					new Transition(s[4], _e[11], s[0])
                    //new Transition(s[5], _e[7], s[6]),
                    //new Transition(s[6], _e[7], s[0])
                }, s[1], "SeqA");

				Seq_producaoB = new DeterministicFiniteAutomaton(new[]
				{
					new Transition(s[1], _e[11], s[2]),
					new Transition(s[2], _e[11], s[3]),
					new Transition(s[3], _e[11], s[4]),
					new Transition(s[4], _e[11], s[5]),
					new Transition(s[5], _e[11], s[0])
                    //new Transition(s[6], _e[7], s[0])
                }, s[1], "SeqB");

				Seq_producaoC = new DeterministicFiniteAutomaton(new[]
				{
					new Transition(s[1], _e[11], s[2]),
					new Transition(s[2], _e[11], s[3]),
					new Transition(s[3], _e[11], s[4]),
					new Transition(s[4], _e[11], s[5]),
					new Transition(s[5], _e[11], s[6]),
					new Transition(s[6], _e[11], s[0])
				}, s[1], "SeqC");
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

				s = Enumerable.Range(0, 8)
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
				/*s = new[]
                {
                    new ExpandedState("0",  0, Marking.Marked),
                    new ExpandedState("1",  1, Marking.Unmarked),
                    new ExpandedState("2",  2, Marking.Unmarked),
                    new ExpandedState("3",  3, Marking.Unmarked),
                    new ExpandedState("4",  4, Marking.Unmarked),
                    new ExpandedState("5",  5, Marking.Unmarked),
                    new ExpandedState("6",  6, Marking.Unmarked)
                };
                */

				Seq_producaoA = new DeterministicFiniteAutomaton(new[]
				{
					new Transition(s[1], _e[11], s[2]),
					new Transition(s[2], _e[11], s[3]),
					new Transition(s[3], _e[11], s[4]),
					new Transition(s[4], _e[11], s[0])
                    //new Transition(s[5], _e[7], s[6]),
                    //new Transition(s[6], _e[7], s[0])
                }, s[1], "SeqA");

				Seq_producaoB = new DeterministicFiniteAutomaton(new[]
				{
					new Transition(s[1], _e[11], s[2]),
					new Transition(s[2], _e[11], s[3]),
					new Transition(s[3], _e[11], s[4]),
					new Transition(s[4], _e[11], s[5]),
					new Transition(s[5], _e[11], s[0])
                    //new Transition(s[6], _e[7], s[0])
                }, s[1], "SeqB");

				Seq_producaoC = new DeterministicFiniteAutomaton(new[]
				{
					new Transition(s[1], _e[11], s[2]),
					new Transition(s[2], _e[11], s[3]),
					new Transition(s[3], _e[11], s[4]),
					new Transition(s[4], _e[11], s[5]),
					new Transition(s[5], _e[11], s[6]),
					new Transition(s[6], _e[11], s[0])
				}, s[1], "SeqC");
			}
		}

		public int Depth => 12;

		public Scheduler InitialScheduler =>
			_e.ToDictionary(kvp => kvp.Value as AbstractEvent,
				kvp => kvp.Value.IsControllable ? 0.0f : float.PositiveInfinity);

		public AbstractState InitialState => Supervisor.InitialState;

		public DFA Supervisor { get; }

		public DFA Seq_producaoA { get; }

		public DFA Seq_producaoB { get; }

		public DFA Seq_producaoC { get; }

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

	internal class CTESsep : ISchedulingProblem     //Define que o problema a ser estudado será o cluster tool Linear Ent/Sai Separada
	{

		public int numcamaras;      // quantidades de camaras no layout

		public int tempocamaras;    // tempo em segundos x 100 de processamento nas camaras

		public int layout;          // 1 = radial 1 robo, 2 = linear E/S Única, 3 = linear E/S Separada e 4 = radial 2 robos

		public int numeventos;

		private readonly Dictionary<int, Event> _e;



		public CTESsep(int parlayout, int partempocamaras, int parnumcamaras)
		{
			// quantidades de camaras no layout
			// Console.WriteLine($"Layout: {parlayout}, tempo da camara: {partempocamaras}, numero de camaras {parnumcamaras}\n");

			//layout = (sequencia[param] % 4) +1;
			//Console.WriteLine($"Num da sequencia: {sequencia[param]}");
			//Console.WriteLine($"Layout: {layout}");
			//tempocamaras = arraytempocamaras[sequencia[param] % 30] * 100;
			//Console.WriteLine($"tempo da camara: {tempocamaras}");

			//System.Threading.Thread.CurrentThread.CurrentCulture = new System.Globalization.CultureInfo("en-US");
			String directory = @"C:\Users\GustavoCaetano\Dropbox\2018_S01\CBA_2018\code_v5\USER\";

			layout = parlayout;
			tempocamaras = partempocamaras;
			numcamaras = parnumcamaras;

			_e = new[]
						 {
						11, 12, 13, 14,
						23, 24,
						103,
						112, 113, 114, 115, 116,
						121, 122, 123, 124, 125, 126,
						131, 132, 133, 134, 135,
						142, 143, 144, 145,
						152, 153, 154, 155,
						162, 163, 164, 165,
						172,
						211, 212, 213, 214, 215, 216,
						221, 222, 223, 224, 225, 226,
						232, 233, 234, 235,
						246,
						311, 312, 313, 314, 315, 316,
						321, 322, 323, 324, 325, 326,
						411, 412, 413, 414, 415,
						426
					}.ToDictionary(alias => alias,
							 alias =>
								 new Event(alias.ToString(),
									 alias % 2 == 0 ? Controllability.Uncontrollable : Controllability.Controllable));

			//seleciona o layout que será trabalhado
			switch (layout)
			{
				case 1: //caso seja layout radial com 1 robo

					//verifica se o problema é para 4,5,6 ou 7 camaras
					;
					if (numcamaras == 4)
					{
						if (File.Exists(directory + "sup4Circ.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton(directory + "sup4Circ.bin");
							var s = new[]
							{
								new ExpandedState("0",  0, Marking.Marked),
								new ExpandedState("1",  1, Marking.Unmarked),
								new ExpandedState("2",  2, Marking.Unmarked),
								new ExpandedState("3",  3, Marking.Unmarked),
								new ExpandedState("4",  4, Marking.Unmarked)
                                //new ExpandedState("5",  5, Marking.Unmarked),
                                // new ExpandedState("6",  6, Marking.Unmarked)
                            };

							Seq_producaoA = new DeterministicFiniteAutomaton(new[]
							{
								new Transition(s[1], _e[13], s[2]),
								new Transition(s[2], _e[13], s[3]),
								new Transition(s[3], _e[13], s[4]),
								new Transition(s[4], _e[13], s[0])
                                //new Transition(s[5], _e[7], s[6]),
                                //new Transition(s[6], _e[7], s[0])
                            }, s[1], "SeqA");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c13 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[133], s[1]),
										 new Transition(s[1], _e[134], s[0])
							},
							s[0], "C13");

							var c14 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[143], s[1]),
										 new Transition(s[1], _e[144], s[0])
							},
							s[0], "C14");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[3]),
										 new Transition(s[3], _e[132], s[0]),
										 new Transition(s[0], _e[135], s[4]),
										 new Transition(s[4], _e[142], s[0]),
										 new Transition(s[0], _e[145], s[5]),
										 new Transition(s[5], _e[152], s[0])
								},
								s[0], "R11");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");

							// E13
							var e13 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[132], s[1]),
										 new Transition(s[1], _e[133], s[0]),
										 new Transition(s[0], _e[134], s[2]),
										 new Transition(s[2], _e[135], s[0])
								},
								s[0], "E13");

							// E14
							var e14 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[142], s[1]),
										 new Transition(s[1], _e[143], s[0]),
										 new Transition(s[0], _e[144], s[2]),
										 new Transition(s[2], _e[145], s[0])
								},
								s[0], "E14");

							// E15
							var e15 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[152], s[1]),
										 new Transition(s[1], _e[13], s[0])
								},
								s[0], "E15");


							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c13, c14, r01, r11 },
								new[] { e10, e11, e12, e13, e14, e15 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup4Circ.bin");
						}

						numeventos = 22;

					}

					if (numcamaras == 5)
					{
						if (File.Exists(directory + "sup5Circ.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton(directory + "sup5Circ.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 7)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c13 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[133], s[1]),
										 new Transition(s[1], _e[134], s[0])
							},
							s[0], "C13");

							var c14 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[143], s[1]),
										 new Transition(s[1], _e[144], s[0])
							},
							s[0], "C14");

							var c15 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[153], s[1]),
										 new Transition(s[1], _e[154], s[0])
							},
							s[0], "C15");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[3]),
										 new Transition(s[3], _e[132], s[0]),
										 new Transition(s[0], _e[135], s[4]),
										 new Transition(s[4], _e[142], s[0]),
										 new Transition(s[0], _e[145], s[5]),
										 new Transition(s[5], _e[152], s[0]),
										 new Transition(s[0], _e[155], s[6]),
										 new Transition(s[6], _e[162], s[0])
								},
								s[0], "R11");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");

							// E13
							var e13 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[132], s[1]),
										 new Transition(s[1], _e[133], s[0]),
										 new Transition(s[0], _e[134], s[2]),
										 new Transition(s[2], _e[135], s[0])
								},
								s[0], "E13");

							// E14
							var e14 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[142], s[1]),
										 new Transition(s[1], _e[143], s[0]),
										 new Transition(s[0], _e[144], s[2]),
										 new Transition(s[2], _e[145], s[0])
								},
								s[0], "E14");

							// E15
							var e15 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[152], s[1]),
										 new Transition(s[1], _e[153], s[0]),
										 new Transition(s[0], _e[154], s[2]),
										 new Transition(s[2], _e[155], s[0])
								},
								s[0], "E15");

							// E16
							var e16 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[162], s[1]),
										 new Transition(s[1], _e[13], s[0])
								},
								s[0], "E16");


							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c13, c14, c15, r01, r11 },
								new[] { e10, e11, e12, e13, e14, e15, e16 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							//Supervisor.ToXMLFile("sup5Circ.xml");

							Utilidades.SerializeAutomaton(Supervisor, "sup5Circ.bin");
						}

						numeventos = 26;

					}

					if (numcamaras == 6)
					{
						if (File.Exists(directory + "sup6Circ.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton(directory + "sup6Circ.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 8)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c13 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[133], s[1]),
										 new Transition(s[1], _e[134], s[0])
							},
							s[0], "C13");

							var c14 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[143], s[1]),
										 new Transition(s[1], _e[144], s[0])
							},
							s[0], "C14");

							var c15 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[153], s[1]),
										 new Transition(s[1], _e[154], s[0])
							},
							s[0], "C15");

							var c16 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[163], s[1]),
										 new Transition(s[1], _e[164], s[0])
							},
							s[0], "C16");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[3]),
										 new Transition(s[3], _e[132], s[0]),
										 new Transition(s[0], _e[135], s[4]),
										 new Transition(s[4], _e[142], s[0]),
										 new Transition(s[0], _e[145], s[5]),
										 new Transition(s[5], _e[152], s[0]),
										 new Transition(s[0], _e[155], s[6]),
										 new Transition(s[6], _e[162], s[0]),
										 new Transition(s[0], _e[165], s[7]),
										 new Transition(s[7], _e[172], s[0])
								},
								s[0], "R11");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");

							// E13
							var e13 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[132], s[1]),
										 new Transition(s[1], _e[133], s[0]),
										 new Transition(s[0], _e[134], s[2]),
										 new Transition(s[2], _e[135], s[0])
								},
								s[0], "E13");

							// E14
							var e14 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[142], s[1]),
										 new Transition(s[1], _e[143], s[0]),
										 new Transition(s[0], _e[144], s[2]),
										 new Transition(s[2], _e[145], s[0])
								},
								s[0], "E14");

							// E15
							var e15 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[152], s[1]),
										 new Transition(s[1], _e[153], s[0]),
										 new Transition(s[0], _e[154], s[2]),
										 new Transition(s[2], _e[155], s[0])
								},
								s[0], "E15");

							// E16
							var e16 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[162], s[1]),
										 new Transition(s[1], _e[163], s[0]),
										 new Transition(s[0], _e[164], s[2]),
										 new Transition(s[2], _e[165], s[0])
								},
								s[0], "E16");

							// E17
							var e17 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[172], s[1]),
										 new Transition(s[1], _e[13], s[0])
								},
								s[0], "E17");


							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c13, c14, c15, c16, r01, r11 },
								new[] { e10, e11, e12, e13, e14, e15, e16, e17 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup6Circ.bin");
							//Supervisor.ToXMLFile("sup6Circ.xml");
						}

						numeventos = 30;

					}

					if (numcamaras == 7)
					{
						if (File.Exists("sup17Circ.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton(directory + "sup7Circ.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 8)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c13 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[133], s[1]),
										 new Transition(s[1], _e[134], s[0])
							},
							s[0], "C13");

							var c14 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[143], s[1]),
										 new Transition(s[1], _e[144], s[0])
							},
							s[0], "C14");

							var c21 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[213], s[1]),
										 new Transition(s[1], _e[214], s[0])
							},
							s[0], "C21");

							var c22 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[223], s[1]),
										 new Transition(s[1], _e[224], s[0])
							},
							s[0], "C22");

							var c23 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[233], s[1]),
										 new Transition(s[1], _e[234], s[0])
							},
							s[0], "C23");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[3]),
										 new Transition(s[3], _e[126], s[0]),
										 new Transition(s[0], _e[131], s[4]),
										 new Transition(s[4], _e[132], s[0]),
										 new Transition(s[0], _e[135], s[5]),
										 new Transition(s[5], _e[142], s[0]),
										 new Transition(s[0], _e[145], s[6]),
										 new Transition(s[6], _e[152], s[0])
								},
								s[0], "R11");

							var r21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[211], s[1]),
										 new Transition(s[1], _e[212], s[0]),
										 new Transition(s[0], _e[215], s[2]),
										 new Transition(s[2], _e[222], s[0]),
										 new Transition(s[0], _e[225], s[3]),
										 new Transition(s[3], _e[232], s[0]),
										 new Transition(s[0], _e[235], s[4]),
										 new Transition(s[4], _e[246], s[0])
								},
								s[0], "R21");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");

							// E13
							var e13 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[132], s[1]),
										 new Transition(s[1], _e[133], s[0]),
										 new Transition(s[0], _e[134], s[2]),
										 new Transition(s[2], _e[135], s[0])
								},
								s[0], "E13");

							// E14
							var e14 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[142], s[1]),
										 new Transition(s[1], _e[143], s[0]),
										 new Transition(s[0], _e[144], s[2]),
										 new Transition(s[2], _e[145], s[0])
								},
								s[0], "E14");

							// E15
							var e15 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[152], s[1]),
										 new Transition(s[1], _e[13], s[0])
								},
								s[0], "E15");

							// E20
							var e20 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[126], s[1]),
										 new Transition(s[1], _e[211], s[0])
								},
								s[0], "E20");

							// E21
							var e21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[212], s[1]),
										 new Transition(s[1], _e[213], s[0]),
										 new Transition(s[0], _e[214], s[2]),
										 new Transition(s[2], _e[215], s[0])
								},
								s[0], "E21");

							// E22
							var e22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[222], s[1]),
										 new Transition(s[1], _e[223], s[0]),
										 new Transition(s[0], _e[224], s[2]),
										 new Transition(s[2], _e[225], s[0])
								},
								s[0], "E22");

							// E23
							var e23 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[232], s[1]),
										 new Transition(s[1], _e[233], s[0]),
										 new Transition(s[0], _e[234], s[2]),
										 new Transition(s[2], _e[235], s[0])
								},
								s[0], "E23");

							// E25
							var e25 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[246], s[1]),
										 new Transition(s[1], _e[131], s[0])
								},
								s[0], "E25");


							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c13, c14, c21, c22, c23, r01, r11, r21 },
								new[] { e10, e11, e12, e13, e14, e15, e20, e21, e22, e23, e25 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup7Circ.bin");
						}

						numeventos = 38;

					}

					break;

				case 2: //caso seja layout linear com E/S única

					//verifica se o problema é para 4,5,6 ou 7 camaras

					if (numcamaras == 4)
					{

						if (File.Exists("sup4linUnic.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton("sup4linUnic.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c21 = new DeterministicFiniteAutomaton(
						   new[]
						   {
										 new Transition(s[0], _e[213], s[1]),
										 new Transition(s[1], _e[214], s[0])
						   },
						   s[0], "C21");

							var c22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[223], s[1]),
										 new Transition(s[1], _e[224], s[0])
								},
								s[0], "C22");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[116], s[0]),
										 new Transition(s[0], _e[121], s[3]),
										 new Transition(s[3], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[4]),
										 new Transition(s[4], _e[132], s[0])
								},
								s[0], "R11");

							var r21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[211], s[1]),
										 new Transition(s[1], _e[212], s[0]),
										 new Transition(s[0], _e[215], s[2]),
										 new Transition(s[2], _e[222], s[0]),
										 new Transition(s[0], _e[225], s[3]),
										 new Transition(s[3], _e[226], s[0])
								},
								s[0], "R21");

							// Especificações

							s = Enumerable.Range(0, 10)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0]),
										 new Transition(s[0], _e[132], s[2]),
										 new Transition(s[2], _e[13], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");


							// E20
							var e20 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[116], s[1]),
										 new Transition(s[1], _e[211], s[0]),
										 new Transition(s[0], _e[226], s[2]),
										 new Transition(s[2], _e[121], s[0])
								},
								s[0], "E20");

							// E21
							var e21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[212], s[1]),
										 new Transition(s[1], _e[213], s[0]),
										 new Transition(s[0], _e[214], s[2]),
										 new Transition(s[2], _e[215], s[0])
								},
								s[0], "E21");

							// E22
							var e22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[222], s[1]),
										 new Transition(s[1], _e[223], s[0]),
										 new Transition(s[0], _e[224], s[2]),
										 new Transition(s[2], _e[225], s[0])
								},
								s[0], "E22");


							Seq_producaoA = new DeterministicFiniteAutomaton(new[]
							{
								new Transition(s[1], _e[13], s[2]),
								new Transition(s[2], _e[13], s[3]),
								new Transition(s[3], _e[13], s[4]),
								new Transition(s[4], _e[13], s[0])
                                //new Transition(s[5], _e[7], s[6]),
                                //new Transition(s[6], _e[7], s[0])
                            }, s[1], "SeqA");

							Seq_producaoB = new DeterministicFiniteAutomaton(new[]
							{
								new Transition(s[1], _e[13], s[2]),
								new Transition(s[2], _e[13], s[3]),
								new Transition(s[3], _e[13], s[4]),
								new Transition(s[4], _e[13], s[5]),
								new Transition(s[5], _e[13], s[0])
                                //new Transition(s[6], _e[7], s[0])
                            }, s[1], "SeqB");

							Seq_producaoC = new DeterministicFiniteAutomaton(new[]
							{
								new Transition(s[1], _e[13], s[2]),
								new Transition(s[2], _e[13], s[3]),
								new Transition(s[3], _e[13], s[4]),
								new Transition(s[4], _e[13], s[5]),
								new Transition(s[5], _e[13], s[6]),
								new Transition(s[6], _e[13], s[0])
							}, s[1], "SeqC");

							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c21, c22, r01, r11, r21 },
								new[] { e10, e11, e12, e21, e22, e20 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup4linUnic.bin");
						}

						numeventos = 26;

					}

					//verifica se o problema é para 4,5,6 ou 7 camaras
					if (numcamaras == 5)
					{

						if (File.Exists("sup5linUnic.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton("sup5linUnic.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c21 = new DeterministicFiniteAutomaton(
						   new[]
						   {
										 new Transition(s[0], _e[213], s[1]),
										 new Transition(s[1], _e[214], s[0])
						   },
						   s[0], "C21");

							var c22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[223], s[1]),
										 new Transition(s[1], _e[224], s[0])
								},
								s[0], "C22");

							var c31 = new DeterministicFiniteAutomaton(
							   new[]
							   {
										 new Transition(s[0], _e[313], s[1]),
										 new Transition(s[1], _e[314], s[0])
							   },
							   s[0], "C31");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[116], s[0]),
										 new Transition(s[0], _e[121], s[3]),
										 new Transition(s[3], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[4]),
										 new Transition(s[4], _e[132], s[0])
								},
								s[0], "R11");

							var r21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[211], s[1]),
										 new Transition(s[1], _e[212], s[0]),
										 new Transition(s[0], _e[215], s[2]),
										 new Transition(s[2], _e[216], s[0]),
										 new Transition(s[0], _e[221], s[3]),
										 new Transition(s[3], _e[222], s[0]),
										 new Transition(s[0], _e[225], s[4]),
										 new Transition(s[4], _e[226], s[0])
								},
								s[0], "R21");

							var r31 = new DeterministicFiniteAutomaton(
							   new[]
							   {
										 new Transition(s[0], _e[311], s[1]),
										 new Transition(s[1], _e[312], s[0]),
										 new Transition(s[0], _e[315], s[2]),
										 new Transition(s[2], _e[316], s[0])
							   },
							   s[0], "R31");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0]),
										 new Transition(s[0], _e[132], s[2]),
										 new Transition(s[2], _e[13], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");


							// E20
							var e20 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[116], s[1]),
										 new Transition(s[1], _e[211], s[0]),
										 new Transition(s[0], _e[226], s[2]),
										 new Transition(s[2], _e[121], s[0])
								},
								s[0], "E20");

							// E21
							var e21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[212], s[1]),
										 new Transition(s[1], _e[213], s[0]),
										 new Transition(s[0], _e[214], s[2]),
										 new Transition(s[2], _e[215], s[0])
								},
								s[0], "E21");

							// E22
							var e22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[222], s[1]),
										 new Transition(s[1], _e[223], s[0]),
										 new Transition(s[0], _e[224], s[2]),
										 new Transition(s[2], _e[225], s[0])
								},
								s[0], "E22");

							// E30
							var e30 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[216], s[1]),
										 new Transition(s[1], _e[311], s[0]),
										 new Transition(s[0], _e[316], s[2]),
										 new Transition(s[2], _e[221], s[0])
								},
								s[0], "E30");

							// E31
							var e31 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[312], s[1]),
										 new Transition(s[1], _e[313], s[0]),
										 new Transition(s[0], _e[314], s[2]),
										 new Transition(s[2], _e[315], s[0])
								},
								s[0], "E31");


							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c21, c22, c31, r01, r11, r21, r31 },
								new[] { e10, e11, e12, e21, e22, e20, e30, e31 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							//Supervisor.ToXMLFile("sup5linUnic.xml");

							Utilidades.SerializeAutomaton(Supervisor, "sup5linUnic.bin");
						}

						numeventos = 34;

					}

					//verifica se o problema é para 4,5,6 ou 7 camaras
					if (numcamaras == 6)
					{

						if (File.Exists("sup6linUnic.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton("sup6linUnic.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c21 = new DeterministicFiniteAutomaton(
						   new[]
						   {
										 new Transition(s[0], _e[213], s[1]),
										 new Transition(s[1], _e[214], s[0])
						   },
						   s[0], "C21");

							var c22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[223], s[1]),
										 new Transition(s[1], _e[224], s[0])
								},
								s[0], "C22");

							var c31 = new DeterministicFiniteAutomaton(
							   new[]
							   {
										 new Transition(s[0], _e[313], s[1]),
										 new Transition(s[1], _e[314], s[0])
							   },
							   s[0], "C31");

							var c32 = new DeterministicFiniteAutomaton(
							   new[]
							   {
										 new Transition(s[0], _e[323], s[1]),
										 new Transition(s[1], _e[324], s[0])
							   },
							   s[0], "C32");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[116], s[0]),
										 new Transition(s[0], _e[121], s[3]),
										 new Transition(s[3], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[4]),
										 new Transition(s[4], _e[132], s[0])
								},
								s[0], "R11");

							var r21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[211], s[1]),
										 new Transition(s[1], _e[212], s[0]),
										 new Transition(s[0], _e[215], s[2]),
										 new Transition(s[2], _e[216], s[0]),
										 new Transition(s[0], _e[221], s[3]),
										 new Transition(s[3], _e[222], s[0]),
										 new Transition(s[0], _e[225], s[4]),
										 new Transition(s[4], _e[226], s[0])
								},
								s[0], "R21");

							var r31 = new DeterministicFiniteAutomaton(
							   new[]
							   {
										 new Transition(s[0], _e[311], s[1]),
										 new Transition(s[1], _e[312], s[0]),
										 new Transition(s[0], _e[315], s[2]),
										 new Transition(s[2], _e[322], s[0]),
										 new Transition(s[0], _e[325], s[3]),
										 new Transition(s[3], _e[326], s[0])
							   },
							   s[0], "R31");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0]),
										 new Transition(s[0], _e[132], s[2]),
										 new Transition(s[2], _e[13], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");


							// E20
							var e20 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[116], s[1]),
										 new Transition(s[1], _e[211], s[0]),
										 new Transition(s[0], _e[226], s[2]),
										 new Transition(s[2], _e[121], s[0])
								},
								s[0], "E20");

							// E21
							var e21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[212], s[1]),
										 new Transition(s[1], _e[213], s[0]),
										 new Transition(s[0], _e[214], s[2]),
										 new Transition(s[2], _e[215], s[0])
								},
								s[0], "E21");

							// E22
							var e22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[222], s[1]),
										 new Transition(s[1], _e[223], s[0]),
										 new Transition(s[0], _e[224], s[2]),
										 new Transition(s[2], _e[225], s[0])
								},
								s[0], "E22");

							// E30
							var e30 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[216], s[1]),
										 new Transition(s[1], _e[311], s[0]),
										 new Transition(s[0], _e[326], s[2]),
										 new Transition(s[2], _e[221], s[0])
								},
								s[0], "E30");

							// E31
							var e31 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[312], s[1]),
										 new Transition(s[1], _e[313], s[0]),
										 new Transition(s[0], _e[314], s[2]),
										 new Transition(s[2], _e[315], s[0])
								},
								s[0], "E31");

							// E32
							var e32 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[322], s[1]),
										 new Transition(s[1], _e[323], s[0]),
										 new Transition(s[0], _e[324], s[2]),
										 new Transition(s[2], _e[325], s[0])
								},
								s[0], "E32");

							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c21, c22, c31, c32, r01, r11, r21, r31 },
								new[] { e10, e11, e12, e21, e22, e20, e30, e31, e32 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup6linUnic.bin");
							//Supervisor.ToXMLFile("sup6linUnic.xml");
						}

						numeventos = 38;

					}

					//verifica se o problema é para 4,5,6 ou 7 camaras
					if (numcamaras == 7)
					{

						if (File.Exists("sup7linUnic.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton("sup7linUnic.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c21 = new DeterministicFiniteAutomaton(
						   new[]
						   {
										 new Transition(s[0], _e[213], s[1]),
										 new Transition(s[1], _e[214], s[0])
						   },
						   s[0], "C21");

							var c22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[223], s[1]),
										 new Transition(s[1], _e[224], s[0])
								},
								s[0], "C22");

							var c31 = new DeterministicFiniteAutomaton(
							   new[]
							   {
										 new Transition(s[0], _e[313], s[1]),
										 new Transition(s[1], _e[314], s[0])
							   },
							   s[0], "C31");

							var c32 = new DeterministicFiniteAutomaton(
							   new[]
							   {
										 new Transition(s[0], _e[323], s[1]),
										 new Transition(s[1], _e[324], s[0])
							   },
							   s[0], "C32");

							var c41 = new DeterministicFiniteAutomaton(
							   new[]
							   {
										 new Transition(s[0], _e[413], s[1]),
										 new Transition(s[1], _e[414], s[0])
							   },
							   s[0], "C41");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[116], s[0]),
										 new Transition(s[0], _e[121], s[3]),
										 new Transition(s[3], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[4]),
										 new Transition(s[4], _e[132], s[0])
								},
								s[0], "R11");

							var r21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[211], s[1]),
										 new Transition(s[1], _e[212], s[0]),
										 new Transition(s[0], _e[215], s[2]),
										 new Transition(s[2], _e[216], s[0]),
										 new Transition(s[0], _e[221], s[3]),
										 new Transition(s[3], _e[222], s[0]),
										 new Transition(s[0], _e[225], s[4]),
										 new Transition(s[4], _e[226], s[0])
								},
								s[0], "R21");

							var r31 = new DeterministicFiniteAutomaton(
							   new[]
							   {
										 new Transition(s[0], _e[311], s[1]),
										 new Transition(s[1], _e[312], s[0]),
										 new Transition(s[0], _e[315], s[2]),
										 new Transition(s[2], _e[316], s[0]),
										 new Transition(s[0], _e[321], s[3]),
										 new Transition(s[3], _e[322], s[0]),
										 new Transition(s[0], _e[325], s[4]),
										 new Transition(s[4], _e[326], s[0])
							   },
							   s[0], "R31");

							var r41 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[411], s[1]),
										 new Transition(s[1], _e[412], s[0]),
										 new Transition(s[0], _e[415], s[2]),
										 new Transition(s[2], _e[426], s[0])
								},
								s[0], "R41");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0]),
										 new Transition(s[0], _e[132], s[2]),
										 new Transition(s[2], _e[13], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");


							// E20
							var e20 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[116], s[1]),
										 new Transition(s[1], _e[211], s[0]),
										 new Transition(s[0], _e[226], s[2]),
										 new Transition(s[2], _e[121], s[0])
								},
								s[0], "E20");

							// E21
							var e21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[212], s[1]),
										 new Transition(s[1], _e[213], s[0]),
										 new Transition(s[0], _e[214], s[2]),
										 new Transition(s[2], _e[215], s[0])
								},
								s[0], "E21");

							// E22
							var e22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[222], s[1]),
										 new Transition(s[1], _e[223], s[0]),
										 new Transition(s[0], _e[224], s[2]),
										 new Transition(s[2], _e[225], s[0])
								},
								s[0], "E22");

							// E30
							var e30 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[216], s[1]),
										 new Transition(s[1], _e[311], s[0]),
										 new Transition(s[0], _e[326], s[2]),
										 new Transition(s[2], _e[221], s[0])
								},
								s[0], "E30");

							// E31
							var e31 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[312], s[1]),
										 new Transition(s[1], _e[313], s[0]),
										 new Transition(s[0], _e[314], s[2]),
										 new Transition(s[2], _e[315], s[0])
								},
								s[0], "E31");

							// E32
							var e32 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[322], s[1]),
										 new Transition(s[1], _e[323], s[0]),
										 new Transition(s[0], _e[324], s[2]),
										 new Transition(s[2], _e[325], s[0])
								},
								s[0], "E32");

							// E40
							var e40 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[316], s[1]),
										 new Transition(s[1], _e[411], s[0]),
										 new Transition(s[0], _e[426], s[2]),
										 new Transition(s[2], _e[321], s[0])
								},
								s[0], "E40");

							// E41
							var e41 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[412], s[1]),
										 new Transition(s[1], _e[413], s[0]),
										 new Transition(s[0], _e[414], s[2]),
										 new Transition(s[2], _e[415], s[0])
								},
								s[0], "E41");

							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c21, c22, c31, c32, c41, r01, r11, r21, r31, r41 },
								new[] { e10, e11, e12, e21, e22, e20, e30, e31, e32, e40, e41 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup7linUnic.bin");
						}

						numeventos = 46;

					}

					break;

				case 3: //caso seja layout linear com E/S separada

					//verifica se o problema é para 4,5,6 ou 7 camaras
					if (numcamaras == 4)
					{

						if (File.Exists("sup4linSep.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton("sup4linSep.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[113], s[1]),
								 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
								 new Transition(s[0], _e[123], s[1]),
								 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c21 = new DeterministicFiniteAutomaton(
						   new[]
						   {
								 new Transition(s[0], _e[213], s[1]),
								 new Transition(s[1], _e[214], s[0])
						   },
						   s[0], "C21");

							var c22 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[223], s[1]),
								 new Transition(s[1], _e[224], s[0])
								},
								s[0], "C22");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[11], s[1]),
								 new Transition(s[1], _e[12], s[0])
								},
								s[0], "R01");

							var r02 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[23], s[1]),
								 new Transition(s[1], _e[24], s[0])
								},
								s[0], "R02");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[103], s[1]),
								 new Transition(s[1], _e[112], s[0]),
								 new Transition(s[0], _e[115], s[2]),
								 new Transition(s[2], _e[122], s[0]),
								 new Transition(s[0], _e[125], s[3]),
								 new Transition(s[3], _e[126], s[0])
								},
								s[0], "R11");

							var r21 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[211], s[1]),
								 new Transition(s[1], _e[212], s[0]),
								 new Transition(s[0], _e[215], s[2]),
								 new Transition(s[2], _e[222], s[0]),
								 new Transition(s[0], _e[225], s[3]),
								 new Transition(s[3], _e[226], s[0])
								},
								s[0], "R21");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[12], s[1]),
								 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[112], s[1]),
								 new Transition(s[1], _e[113], s[0]),
								 new Transition(s[0], _e[114], s[2]),
								 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[122], s[1]),
								 new Transition(s[1], _e[123], s[0]),
								 new Transition(s[0], _e[124], s[2]),
								 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");


							// E20
							var e20 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[126], s[1]),
								 new Transition(s[1], _e[211], s[0])
								},
								s[0], "E20");

							// E21
							var e21 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[212], s[1]),
								 new Transition(s[1], _e[213], s[0]),
								 new Transition(s[0], _e[214], s[2]),
								 new Transition(s[2], _e[215], s[0])
								},
								s[0], "E21");

							// E22
							var e22 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[222], s[1]),
								 new Transition(s[1], _e[223], s[0]),
								 new Transition(s[0], _e[224], s[2]),
								 new Transition(s[2], _e[225], s[0])
								},
								s[0], "E22");

							// E30
							var e30 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[226], s[1]),
								 new Transition(s[1], _e[23], s[0])
								},
								s[0], "E30");



							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c21, c22, r01, r02, r11, r21 },
								new[] { e10, e30, e11, e12, e20, e21, e22 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup4linSep.bin");
						}

						numeventos = 24;

					}

					//verifica se o problema é para 4,5,6 ou 7 camaras
					if (numcamaras == 5)
					{

						if (File.Exists("sup5linSep.bin"))
						//if (false)
						{

							Supervisor = Utilidades.DeserializeAutomaton("sup5linSep.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[113], s[1]),
								 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
								 new Transition(s[0], _e[123], s[1]),
								 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c21 = new DeterministicFiniteAutomaton(
						   new[]
						   {
								 new Transition(s[0], _e[213], s[1]),
								 new Transition(s[1], _e[214], s[0])
						   },
						   s[0], "C21");

							var c22 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[223], s[1]),
								 new Transition(s[1], _e[224], s[0])
								},
								s[0], "C22");

							var c31 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[313], s[1]),
								 new Transition(s[1], _e[314], s[0])
								},
								s[0], "C31");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[11], s[1]),
								 new Transition(s[1], _e[12], s[0])
								},
								s[0], "R01");

							var r02 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[23], s[1]),
								 new Transition(s[1], _e[24], s[0])
								},
								s[0], "R02");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[103], s[1]),
								 new Transition(s[1], _e[112], s[0]),
								 new Transition(s[0], _e[115], s[2]),
								 new Transition(s[2], _e[122], s[0]),
								 new Transition(s[0], _e[125], s[3]),
								 new Transition(s[3], _e[126], s[0])
								},
								s[0], "R11");

							var r21 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[211], s[1]),
								 new Transition(s[1], _e[212], s[0]),
								 new Transition(s[0], _e[215], s[2]),
								 new Transition(s[2], _e[222], s[0]),
								 new Transition(s[0], _e[225], s[3]),
								 new Transition(s[3], _e[226], s[0])
								},
								s[0], "R21");

							var r31 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[311], s[1]),
								 new Transition(s[1], _e[312], s[0]),
								 new Transition(s[0], _e[315], s[2]),
								 new Transition(s[2], _e[316], s[0])
								},
								s[0], "R31");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[12], s[1]),
								 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[112], s[1]),
								 new Transition(s[1], _e[113], s[0]),
								 new Transition(s[0], _e[114], s[2]),
								 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[122], s[1]),
								 new Transition(s[1], _e[123], s[0]),
								 new Transition(s[0], _e[124], s[2]),
								 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");


							// E20
							var e20 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[126], s[1]),
								 new Transition(s[1], _e[211], s[0])
								},
								s[0], "E20");

							// E21
							var e21 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[212], s[1]),
								 new Transition(s[1], _e[213], s[0]),
								 new Transition(s[0], _e[214], s[2]),
								 new Transition(s[2], _e[215], s[0])
								},
								s[0], "E21");

							// E22
							var e22 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[222], s[1]),
								 new Transition(s[1], _e[223], s[0]),
								 new Transition(s[0], _e[224], s[2]),
								 new Transition(s[2], _e[225], s[0])
								},
								s[0], "E22");

							// E30
							var e30 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[226], s[1]),
								 new Transition(s[1], _e[311], s[0])
								},
								s[0], "E30");

							// E31
							var e31 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[312], s[1]),
								 new Transition(s[1], _e[313], s[0]),
								 new Transition(s[0], _e[314], s[2]),
								 new Transition(s[2], _e[315], s[0])
								},
								s[0], "E31");

							// E40
							var e40 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[316], s[1]),
								 new Transition(s[1], _e[23], s[0])
								},
								s[0], "E40");



							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c21, c22, c31, r01, r02, r11, r21, r31 },
								new[] { e10, e30, e11, e12, e20, e21, e22, e31, e40 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							//Supervisor.ToXMLFile("sup5linSep.xml");

							Utilidades.SerializeAutomaton(Supervisor, "sup5linSep.bin");
						}

						numeventos = 30;

					}

					//verifica se o problema é para 4,5,6 ou 7 camaras
					if (numcamaras == 6)
					{

						if (File.Exists("sup6linSep.bin"))
						//if (false)
						{

							Supervisor = Utilidades.DeserializeAutomaton("sup6linSep.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[113], s[1]),
								 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
								 new Transition(s[0], _e[123], s[1]),
								 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c21 = new DeterministicFiniteAutomaton(
						   new[]
						   {
								 new Transition(s[0], _e[213], s[1]),
								 new Transition(s[1], _e[214], s[0])
						   },
						   s[0], "C21");

							var c22 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[223], s[1]),
								 new Transition(s[1], _e[224], s[0])
								},
								s[0], "C22");

							var c31 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[313], s[1]),
								 new Transition(s[1], _e[314], s[0])
								},
								s[0], "C31");

							var c32 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[323], s[1]),
								 new Transition(s[1], _e[324], s[0])
								},
								s[0], "C32");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[11], s[1]),
								 new Transition(s[1], _e[12], s[0])
								},
								s[0], "R01");

							var r02 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[23], s[1]),
								 new Transition(s[1], _e[24], s[0])
								},
								s[0], "R02");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[103], s[1]),
								 new Transition(s[1], _e[112], s[0]),
								 new Transition(s[0], _e[115], s[2]),
								 new Transition(s[2], _e[122], s[0]),
								 new Transition(s[0], _e[125], s[3]),
								 new Transition(s[3], _e[126], s[0])
								},
								s[0], "R11");

							var r21 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[211], s[1]),
								 new Transition(s[1], _e[212], s[0]),
								 new Transition(s[0], _e[215], s[2]),
								 new Transition(s[2], _e[222], s[0]),
								 new Transition(s[0], _e[225], s[3]),
								 new Transition(s[3], _e[226], s[0])
								},
								s[0], "R21");

							var r31 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[311], s[1]),
								 new Transition(s[1], _e[312], s[0]),
								 new Transition(s[0], _e[315], s[2]),
								 new Transition(s[2], _e[322], s[0]),
								 new Transition(s[0], _e[325], s[3]),
								 new Transition(s[3], _e[326], s[0])
								},
								s[0], "R31");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[12], s[1]),
								 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[112], s[1]),
								 new Transition(s[1], _e[113], s[0]),
								 new Transition(s[0], _e[114], s[2]),
								 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[122], s[1]),
								 new Transition(s[1], _e[123], s[0]),
								 new Transition(s[0], _e[124], s[2]),
								 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");


							// E20
							var e20 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[126], s[1]),
								 new Transition(s[1], _e[211], s[0])
								},
								s[0], "E20");

							// E21
							var e21 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[212], s[1]),
								 new Transition(s[1], _e[213], s[0]),
								 new Transition(s[0], _e[214], s[2]),
								 new Transition(s[2], _e[215], s[0])
								},
								s[0], "E21");

							// E22
							var e22 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[222], s[1]),
								 new Transition(s[1], _e[223], s[0]),
								 new Transition(s[0], _e[224], s[2]),
								 new Transition(s[2], _e[225], s[0])
								},
								s[0], "E22");

							// E30
							var e30 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[226], s[1]),
								 new Transition(s[1], _e[311], s[0])
								},
								s[0], "E30");

							// E31
							var e31 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[312], s[1]),
								 new Transition(s[1], _e[313], s[0]),
								 new Transition(s[0], _e[314], s[2]),
								 new Transition(s[2], _e[315], s[0])
								},
								s[0], "E31");

							// E32
							var e32 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[322], s[1]),
								 new Transition(s[1], _e[323], s[0]),
								 new Transition(s[0], _e[324], s[2]),
								 new Transition(s[2], _e[325], s[0])
								},
								s[0], "E32");

							// E40
							var e40 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[326], s[1]),
								 new Transition(s[1], _e[23], s[0])
								},
								s[0], "E40");



							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c21, c22, c31, c32, r01, r02, r11, r21, r31 },
								new[] { e10, e40, e11, e12, e21, e22, e31, e32, e20, e30 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup6linSep.bin");
							//Supervisor.ToXMLFile("sup6linSep.xml");
						}

						numeventos = 34;

					}

					//verifica se o problema é para 4,5,6 ou 7 camaras
					if (numcamaras == 7)
					{

						if (File.Exists("sup7linSep.bin"))
						//if (false)
						{

							Supervisor = Utilidades.DeserializeAutomaton("sup7linSep.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[113], s[1]),
								 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
								 new Transition(s[0], _e[123], s[1]),
								 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c21 = new DeterministicFiniteAutomaton(
						   new[]
						   {
								 new Transition(s[0], _e[213], s[1]),
								 new Transition(s[1], _e[214], s[0])
						   },
						   s[0], "C21");

							var c22 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[223], s[1]),
								 new Transition(s[1], _e[224], s[0])
								},
								s[0], "C22");

							var c31 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[313], s[1]),
								 new Transition(s[1], _e[314], s[0])
								},
								s[0], "C31");

							var c32 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[323], s[1]),
								 new Transition(s[1], _e[324], s[0])
								},
								s[0], "C32");

							var c41 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[413], s[1]),
								 new Transition(s[1], _e[414], s[0])
								},
								s[0], "C41");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[11], s[1]),
								 new Transition(s[1], _e[12], s[0])
								},
								s[0], "R01");

							var r02 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[23], s[1]),
								 new Transition(s[1], _e[24], s[0])
								},
								s[0], "R02");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[103], s[1]),
								 new Transition(s[1], _e[112], s[0]),
								 new Transition(s[0], _e[115], s[2]),
								 new Transition(s[2], _e[122], s[0]),
								 new Transition(s[0], _e[125], s[3]),
								 new Transition(s[3], _e[126], s[0])
								},
								s[0], "R11");

							var r21 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[211], s[1]),
								 new Transition(s[1], _e[212], s[0]),
								 new Transition(s[0], _e[215], s[2]),
								 new Transition(s[2], _e[222], s[0]),
								 new Transition(s[0], _e[225], s[3]),
								 new Transition(s[3], _e[226], s[0])
								},
								s[0], "R21");

							var r31 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[311], s[1]),
								 new Transition(s[1], _e[312], s[0]),
								 new Transition(s[0], _e[315], s[2]),
								 new Transition(s[2], _e[322], s[0]),
								 new Transition(s[0], _e[325], s[3]),
								 new Transition(s[3], _e[326], s[0])
								},
								s[0], "R31");

							var r41 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[411], s[1]),
								 new Transition(s[1], _e[412], s[0]),
								 new Transition(s[0], _e[415], s[2]),
								 new Transition(s[2], _e[426], s[0])
								},
								s[0], "R41");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[12], s[1]),
								 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[112], s[1]),
								 new Transition(s[1], _e[113], s[0]),
								 new Transition(s[0], _e[114], s[2]),
								 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[122], s[1]),
								 new Transition(s[1], _e[123], s[0]),
								 new Transition(s[0], _e[124], s[2]),
								 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");


							// E20
							var e20 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[126], s[1]),
								 new Transition(s[1], _e[211], s[0])
								},
								s[0], "E20");

							// E21
							var e21 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[212], s[1]),
								 new Transition(s[1], _e[213], s[0]),
								 new Transition(s[0], _e[214], s[2]),
								 new Transition(s[2], _e[215], s[0])
								},
								s[0], "E21");

							// E22
							var e22 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[222], s[1]),
								 new Transition(s[1], _e[223], s[0]),
								 new Transition(s[0], _e[224], s[2]),
								 new Transition(s[2], _e[225], s[0])
								},
								s[0], "E22");

							// E30
							var e30 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[226], s[1]),
								 new Transition(s[1], _e[311], s[0])
								},
								s[0], "E30");

							// E31
							var e31 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[312], s[1]),
								 new Transition(s[1], _e[313], s[0]),
								 new Transition(s[0], _e[314], s[2]),
								 new Transition(s[2], _e[315], s[0])
								},
								s[0], "E31");

							// E32
							var e32 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[322], s[1]),
								 new Transition(s[1], _e[323], s[0]),
								 new Transition(s[0], _e[324], s[2]),
								 new Transition(s[2], _e[325], s[0])
								},
								s[0], "E32");

							// E40
							var e40 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[326], s[1]),
								 new Transition(s[1], _e[411], s[0])
								},
								s[0], "E40");

							// E41
							var e41 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[412], s[1]),
								 new Transition(s[1], _e[413], s[0]),
								 new Transition(s[0], _e[414], s[2]),
								 new Transition(s[2], _e[415], s[0])
								},
								s[0], "E41");

							// E50
							var e50 = new DeterministicFiniteAutomaton(
								new[]
								{
								 new Transition(s[0], _e[426], s[1]),
								 new Transition(s[1], _e[23], s[0])
								},
								s[0], "E50");

							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c21, c22, c31, c32, c41, r01, r02, r11, r21, r31, r41 },
								new[] { e10, e20, e30, e40, e50, e11, e12, e21, e22, e31, e32, e41 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup7linSep.bin");
						}

						numeventos = 40;

					}

					break;

				case 4: //caso seja layout radial com 2 robos

					//verifica se o problema é para 4,5,6 ou 7 camaras
					if (numcamaras == 4)
					{

						if (File.Exists(directory + "sup4Circ2Robos.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton(directory + "sup4Circ2Robos.bin");
							//Console.Write("\n\n tudo ok \n")
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c13 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[133], s[1]),
										 new Transition(s[1], _e[134], s[0])
							},
							s[0], "C13");

							var c14 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[143], s[1]),
										 new Transition(s[1], _e[144], s[0])
							},
							s[0], "C14");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[3]),
										 new Transition(s[3], _e[132], s[0])
								},
								s[0], "R11");

							var r12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[135], s[1]),
										 new Transition(s[1], _e[142], s[0]),
										 new Transition(s[0], _e[145], s[2]),
										 new Transition(s[2], _e[152], s[0])
								},
								s[0], "R12");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");

							// E13
							var e13 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[132], s[1]),
										 new Transition(s[1], _e[133], s[0]),
										 new Transition(s[0], _e[134], s[2]),
										 new Transition(s[2], _e[135], s[0])
								},
								s[0], "E13");

							//E14
							var e14 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[142], s[1]),
										 new Transition(s[1], _e[143], s[0]),
										 new Transition(s[0], _e[144], s[2]),
										 new Transition(s[2], _e[145], s[0])
								},
								s[0], "E14");

							//E15
							var e15 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[152], s[1]),
										 new Transition(s[1], _e[13], s[0])
								},
								s[0], "E15");


							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c13, c14, r01, r11, r12 },
								new[] { e10, e11, e12, e13, e14, e15 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup4Circ2Robos.bin");
						}

						numeventos = 22;

					}

					//verifica se o problema é para 4,5,6 ou 7 camaras
					if (numcamaras == 5)
					{

						if (File.Exists(directory + "sup51Circ2Robos.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton(directory + "sup5Circ2Robos.bin");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c13 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[133], s[1]),
										 new Transition(s[1], _e[134], s[0])
							},
							s[0], "C13");

							var c14 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[143], s[1]),
										 new Transition(s[1], _e[144], s[0])
							},
							s[0], "C14");

							var c15 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[153], s[1]),
										 new Transition(s[1], _e[154], s[0])
							},
							s[0], "C15");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[3]),
										 new Transition(s[3], _e[132], s[0])
								},
								s[0], "R11");

							var r12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[135], s[1]),
										 new Transition(s[1], _e[142], s[0]),
										 new Transition(s[0], _e[145], s[2]),
										 new Transition(s[2], _e[152], s[0]),
										 new Transition(s[0], _e[155], s[3]),
										 new Transition(s[3], _e[162], s[0])
								},
								s[0], "R12");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");

							// E13
							var e13 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[132], s[1]),
										 new Transition(s[1], _e[133], s[0]),
										 new Transition(s[0], _e[134], s[2]),
										 new Transition(s[2], _e[135], s[0])
								},
								s[0], "E13");

							//E14
							var e14 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[142], s[1]),
										 new Transition(s[1], _e[143], s[0]),
										 new Transition(s[0], _e[144], s[2]),
										 new Transition(s[2], _e[145], s[0])
								},
								s[0], "E14");

							//E15
							var e15 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[152], s[1]),
										 new Transition(s[1], _e[153], s[0]),
										 new Transition(s[0], _e[154], s[2]),
										 new Transition(s[2], _e[155], s[0])
								},
								s[0], "E15");

							//E16
							var e16 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[162], s[1]),
										 new Transition(s[1], _e[13], s[0])
								},
								s[0], "E16");


							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c13, c14, c15, r01, r11, r12 },
								new[] { e10, e11, e12, e13, e14, e15, e16 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							//Supervisor.ToXMLFile("sup5Circ2Robos.xml");

							Utilidades.SerializeAutomaton(Supervisor, "sup5Circ2Robos.bin");
						}
						numeventos = 26;
					}

					//verifica se o problema é para 4,5,6 ou 7 camaras
					if (numcamaras == 6)
					{

						if (File.Exists(directory + "sup6Circ2Robos.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton(directory + "sup6Circ2Robos.bin");
							//Console.Write("\n\n tudo ok \n");
						}
						else
						{
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 6)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c13 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[133], s[1]),
										 new Transition(s[1], _e[134], s[0])
							},
							s[0], "C13");

							var c14 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[143], s[1]),
										 new Transition(s[1], _e[144], s[0])
							},
							s[0], "C14");

							var c15 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[153], s[1]),
										 new Transition(s[1], _e[154], s[0])
							},
							s[0], "C15");

							var c16 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[163], s[1]),
										 new Transition(s[1], _e[164], s[0])
							},
							s[0], "C16");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[3]),
										 new Transition(s[3], _e[132], s[0])
								},
								s[0], "R11");

							var r12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[135], s[1]),
										 new Transition(s[1], _e[142], s[0]),
										 new Transition(s[0], _e[145], s[2]),
										 new Transition(s[2], _e[152], s[0]),
										 new Transition(s[0], _e[155], s[3]),
										 new Transition(s[3], _e[162], s[0]),
										 new Transition(s[0], _e[165], s[4]),
										 new Transition(s[4], _e[172], s[0])
								},
								s[0], "R12");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");

							// E13
							var e13 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[132], s[1]),
										 new Transition(s[1], _e[133], s[0]),
										 new Transition(s[0], _e[134], s[2]),
										 new Transition(s[2], _e[135], s[0])
								},
								s[0], "E13");

							//E14
							var e14 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[142], s[1]),
										 new Transition(s[1], _e[143], s[0]),
										 new Transition(s[0], _e[144], s[2]),
										 new Transition(s[2], _e[145], s[0])
								},
								s[0], "E14");

							//E15
							var e15 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[152], s[1]),
										 new Transition(s[1], _e[153], s[0]),
										 new Transition(s[0], _e[154], s[2]),
										 new Transition(s[2], _e[155], s[0])
								},
								s[0], "E15");

							//E16
							var e16 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[162], s[1]),
										 new Transition(s[1], _e[163], s[0]),
										 new Transition(s[0], _e[164], s[2]),
										 new Transition(s[2], _e[165], s[0])
								},
								s[0], "E16");

							//E17
							var e17 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[172], s[1]),
										 new Transition(s[1], _e[13], s[0])
								},
								s[0], "E17");


							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c13, c14, c15, c16, r01, r11, r12 },
								new[] { e10, e11, e12, e13, e14, e15, e16, e17 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup6Circ2Robos.bin");
							//Supervisor.ToXMLFile("sup6Circ2Robos.xml");
						}

						numeventos = 30;

					}

					if (numcamaras == 7)
					{

						if (File.Exists("sup7Circ2Robos.bin"))
						//if (false)
						{
							Supervisor = Utilidades.DeserializeAutomaton(directory + "sup7Circ2Robos.bin");
							//Console.Write("\n\n tudo ok ok \n \n");
						}
						else
						{
							Console.Write("\n\n to no else \n \n");
							Stopwatch timersup = new Stopwatch();
							timersup.Start();

							var s = Enumerable.Range(0, 7)
						   .ToDictionary(i => i,
							   i => new ExpandedState(i.ToString(), i == 0 ? 0u : 1u, i == 0 ? Marking.Marked : Marking.Unmarked));

							// CAMARAS
							var c11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[113], s[1]),
										 new Transition(s[1], _e[114], s[0])
								},
								s[0], "C11");

							var c12 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[123], s[1]),
										 new Transition(s[1], _e[124], s[0])
							},
							s[0], "C12");

							var c13 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[133], s[1]),
										 new Transition(s[1], _e[134], s[0])
							},
							s[0], "C13");

							var c14 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[143], s[1]),
										 new Transition(s[1], _e[144], s[0])
							},
							s[0], "C14");

							var c21 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[213], s[1]),
										 new Transition(s[1], _e[214], s[0])
							},
							s[0], "C21");

							var c22 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[223], s[1]),
										 new Transition(s[1], _e[224], s[0])
							},
							s[0], "C22");

							var c23 = new DeterministicFiniteAutomaton(
							new[]
							{
										 new Transition(s[0], _e[233], s[1]),
										 new Transition(s[1], _e[234], s[0])
							},
							s[0], "C23");

							// ROBOS
							var r01 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[11], s[1]),
										 new Transition(s[1], _e[12], s[0]),
										 new Transition(s[0], _e[13], s[2]),
										 new Transition(s[2], _e[14], s[0])
								},
								s[0], "R01");

							var r11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[103], s[1]),
										 new Transition(s[1], _e[112], s[0]),
										 new Transition(s[0], _e[115], s[2]),
										 new Transition(s[2], _e[122], s[0]),
										 new Transition(s[0], _e[125], s[3]),
										 new Transition(s[3], _e[126], s[0])
								},
								s[0], "R11");

							var r12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[131], s[1]),
										 new Transition(s[1], _e[132], s[0]),
										 new Transition(s[0], _e[135], s[2]),
										 new Transition(s[2], _e[142], s[0]),
										 new Transition(s[0], _e[145], s[3]),
										 new Transition(s[3], _e[152], s[0])
								},
								s[0], "R12");

							var r21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[211], s[1]),
										 new Transition(s[1], _e[212], s[0]),
										 new Transition(s[0], _e[215], s[2]),
										 new Transition(s[2], _e[222], s[0])
								},
								s[0], "R21");

							var r22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[225], s[1]),
										 new Transition(s[1], _e[232], s[0]),
										 new Transition(s[0], _e[235], s[2]),
										 new Transition(s[2], _e[246], s[0])
								},
								s[0], "R22");

							// Especificações

							s = Enumerable.Range(0, 6)
							   .ToDictionary(i => i,
								   i => new ExpandedState(i.ToString(), 0, i == 0 ? Marking.Marked : Marking.Unmarked));

							// E10
							var e10 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[12], s[1]),
										 new Transition(s[1], _e[103], s[0])
								},
								s[0], "E10");

							// E11
							var e11 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[112], s[1]),
										 new Transition(s[1], _e[113], s[0]),
										 new Transition(s[0], _e[114], s[2]),
										 new Transition(s[2], _e[115], s[0])
								},
								s[0], "E11");

							// E12
							var e12 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[122], s[1]),
										 new Transition(s[1], _e[123], s[0]),
										 new Transition(s[0], _e[124], s[2]),
										 new Transition(s[2], _e[125], s[0])
								},
								s[0], "E12");

							// E13
							var e13 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[132], s[1]),
										 new Transition(s[1], _e[133], s[0]),
										 new Transition(s[0], _e[134], s[2]),
										 new Transition(s[2], _e[135], s[0])
								},
								s[0], "E13");

							// E14
							var e14 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[142], s[1]),
										 new Transition(s[1], _e[143], s[0]),
										 new Transition(s[0], _e[144], s[2]),
										 new Transition(s[2], _e[145], s[0])
								},
								s[0], "E14");

							// E15
							var e15 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[152], s[1]),
										 new Transition(s[1], _e[13], s[0])
								},
								s[0], "E15");

							// E20
							var e20 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[126], s[1]),
										 new Transition(s[1], _e[211], s[0])
								},
								s[0], "E20");

							// E21
							var e21 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[212], s[1]),
										 new Transition(s[1], _e[213], s[0]),
										 new Transition(s[0], _e[214], s[2]),
										 new Transition(s[2], _e[215], s[0])
								},
								s[0], "E21");

							// E22
							var e22 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[222], s[1]),
										 new Transition(s[1], _e[223], s[0]),
										 new Transition(s[0], _e[224], s[2]),
										 new Transition(s[2], _e[225], s[0])
								},
								s[0], "E22");

							// E23
							var e23 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[232], s[1]),
										 new Transition(s[1], _e[233], s[0]),
										 new Transition(s[0], _e[234], s[2]),
										 new Transition(s[2], _e[235], s[0])
								},
								s[0], "E23");

							// E25
							var e25 = new DeterministicFiniteAutomaton(
								new[]
								{
										 new Transition(s[0], _e[246], s[1]),
										 new Transition(s[1], _e[131], s[0])
								},
								s[0], "E25");


							Supervisor = DFA.MonolithicSupervisor(new[] { c11, c12, c13, c14, c21, c22, c23, r01, r11, r12, r21, r22 },
								new[] { e10, e11, e12, e13, e14, e15, e20, e21, e22, e23, e25 }, true);

							timersup.Stop();
							Console.WriteLine($"Tempo de computação do supervisor: {timersup.ElapsedMilliseconds / 1000.0} s");

							Utilidades.SerializeAutomaton(Supervisor, "sup7Circ2Robos.bin");
							Console.Write("\n \n nada ok \n \n");
						}

						numeventos = 38;

					}

					break;
			}
		}

		private DFA FromXMLFile(string v)
		{
			throw new NotImplementedException();
		}

		public DFA Supervisor { get; }

		public DFA Seq_producaoA { get; }

		public DFA Seq_producaoB { get; }

		public DFA Seq_producaoC { get; }

		public int Depth => numeventos;  //Numero de eventos para produzir um wafer na configuração linear ent/sai separada

		public AbstractState InitialState => Supervisor.InitialState;

		public AbstractState TargetState => Supervisor.InitialState;

		public Restriction InitialRestrition(int products)  // Define o número máximo de vezes que os eventos podem ocorrer
		{
			return new Restriction
			{
				{_e[11], (uint) (1*products)},
				{_e[12], (uint) (1*products)},
				{_e[13], (uint) (1*products)},
				{_e[14], (uint) (1*products)},
				{_e[23], (uint) (1*products)},
				{_e[24], (uint) (1*products)},
				{_e[103], (uint) (1*products)},
				{_e[112], (uint) (1*products)},
				{_e[113], (uint) (1*products)},
				{_e[114], (uint) (1*products)},
				{_e[115], (uint) (1*products)},
				{_e[116], (uint) (1*products)},
				{_e[121], (uint) (1*products)},
				{_e[122], (uint) (1*products)},
				{_e[123], (uint) (1*products)},
				{_e[124], (uint) (1*products)},
				{_e[125], (uint) (1*products)},
				{_e[126], (uint) (1*products)},
				{_e[131], (uint) (1*products)},
				{_e[132], (uint) (1*products)},
				{_e[133], (uint) (1*products)},
				{_e[134], (uint) (1*products)},
				{_e[135], (uint) (1*products)},
				{_e[142], (uint) (1*products)},
				{_e[143], (uint) (1*products)},
				{_e[144], (uint) (1*products)},
				{_e[145], (uint) (1*products)},
				{_e[152], (uint) (1*products)},
				{_e[153], (uint) (1*products)},
				{_e[154], (uint) (1*products)},
				{_e[155], (uint) (1*products)},
				{_e[162], (uint) (1*products)},
				{_e[163], (uint) (1*products)},
				{_e[164], (uint) (1*products)},
				{_e[165], (uint) (1*products)},
				{_e[172], (uint) (1*products)},
				{_e[211], (uint) (1*products)},
				{_e[212], (uint) (1*products)},
				{_e[213], (uint) (1*products)},
				{_e[214], (uint) (1*products)},
				{_e[215], (uint) (1*products)},
				{_e[216], (uint) (1*products)},
				{_e[221], (uint) (1*products)},
				{_e[222], (uint) (1*products)},
				{_e[223], (uint) (1*products)},
				{_e[224], (uint) (1*products)},
				{_e[225], (uint) (1*products)},
				{_e[226], (uint) (1*products)},
				{_e[232], (uint) (1*products)},
				{_e[233], (uint) (1*products)},
				{_e[234], (uint) (1*products)},
				{_e[235], (uint) (1*products)},
				{_e[246], (uint) (1*products)},
				{_e[311], (uint) (1*products)},
				{_e[312], (uint) (1*products)},
				{_e[313], (uint) (1*products)},
				{_e[314], (uint) (1*products)},
				{_e[315], (uint) (1*products)},
				{_e[316], (uint) (1*products)},
				{_e[321], (uint) (1*products)},
				{_e[322], (uint) (1*products)},
				{_e[323], (uint) (1*products)},
				{_e[324], (uint) (1*products)},
				{_e[325], (uint) (1*products)},
				{_e[326], (uint) (1*products)},
				{_e[411], (uint) (1*products)},
				{_e[412], (uint) (1*products)},
				{_e[413], (uint) (1*products)},
				{_e[414], (uint) (1*products)},
				{_e[415], (uint) (1*products)},
				{_e[426], (uint) (1*products)}
			};
		}

		public Scheduler InitialScheduler =>        //Inicializa Escalonamento de eventos
				_e.ToDictionary(kvp => kvp.Value as AbstractEvent,
					kvp => kvp.Value.IsControllable ? 0.0f : float.PositiveInfinity);

		public Update UpdateFunction => (old, ev) => //??????????? Escalonamento de eventos ?????
		{
			var sch = old.ToDictionary(kvp => kvp.Key, kvp =>
			{
				var v = kvp.Value - old[ev];

				if (kvp.Key.IsControllable) return v < 0 ? 0 : v;
				if (v < 0) return float.NaN;
				return v;
			});

			if (!ev.IsControllable) sch[ev] = float.PositiveInfinity;

			switch (layout)
			{
				case 1: //caso seja layout radial com 1 robo

					if (numcamaras == 4)
					{
						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 474;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variavel
								break;
							case "115":
								sch[_e[122]] = 739;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variavel
								break;
							case "125":
								sch[_e[132]] = 781;
								break;
							case "133":
								sch[_e[134]] = tempocamaras; //variavel
								break;
							case "135":
								sch[_e[142]] = 781;
								break;
							case "143":
								sch[_e[144]] = tempocamaras; //variavel
								break;
							case "145":
								sch[_e[152]] = 690;
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					if (numcamaras == 5)
					{
						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 454;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variavel
								break;
							case "115":
								sch[_e[122]] = 700;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variavel
								break;
							case "125":
								sch[_e[132]] = 741;
								break;
							case "133":
								sch[_e[134]] = tempocamaras; //variavel
								break;
							case "135":
								sch[_e[142]] = 768;
								break;
							case "143":
								sch[_e[144]] = tempocamaras; //variavel
								break;
							case "145":
								sch[_e[152]] = 768;
								break;
							case "153":
								sch[_e[154]] = tempocamaras; //variavel
								break;
							case "155":
								sch[_e[162]] = 700; //variavel
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					if (numcamaras == 6)
					{
						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 454;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variavel
								break;
							case "115":
								sch[_e[122]] = 700;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variavel
								break;
							case "125":
								sch[_e[132]] = 741;
								break;
							case "133":
								sch[_e[134]] = tempocamaras; //variavel
								break;
							case "135":
								sch[_e[142]] = 768;
								break;
							case "143":
								sch[_e[144]] = tempocamaras; //variavel
								break;
							case "145":
								sch[_e[152]] = 768;
								break;
							case "153":
								sch[_e[154]] = tempocamaras; //variavel
								break;
							case "155":
								sch[_e[162]] = 741; //variavel
								break;
							case "163":
								sch[_e[164]] = tempocamaras; //variavel
								break;
							case "165":
								sch[_e[172]] = 599; //variavel
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					if (numcamaras == 7)
					{
						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 454;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variavel
								break;
							case "115":
								sch[_e[122]] = 700;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variavel
								break;
							case "125":
								sch[_e[126]] = 692;
								break;
							case "211":
								sch[_e[212]] = 623;
								break;
							case "213":
								sch[_e[214]] = tempocamaras; //variavel
								break;
							case "215":
								sch[_e[222]] = 739;
								break;
							case "223":
								sch[_e[224]] = tempocamaras; //variavel
								break;
							case "225":
								sch[_e[232]] = 781;
								break;
							case "233":
								sch[_e[234]] = tempocamaras; //variavel
								break;
							case "235":
								sch[_e[246]] = 761;
								break;
							case "131":
								sch[_e[132]] = 719;
								break;
							case "133":
								sch[_e[134]] = tempocamaras; //variavel
								break;
							case "135":
								sch[_e[142]] = 741;
								break;
							case "143":
								sch[_e[144]] = tempocamaras; //variavel
								break;
							case "145":
								sch[_e[152]] = 651; //variavel
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					break;

				case 2: //caso seja layout linear com E/S única

					if (numcamaras == 4)
					{

						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 508;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variável
								break;
							case "115":
								sch[_e[116]] = 751;
								break;
							case "211":
								sch[_e[212]] = 669;
								break;
							case "213":
								sch[_e[214]] = tempocamaras; //variável
								break;
							case "215":
								sch[_e[222]] = 832;
								break;
							case "223":
								sch[_e[224]] = tempocamaras; //variável
								break;
							case "225":
								sch[_e[226]] = 669;
								break;
							case "121":
								sch[_e[122]] = 751;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variável
								break;
							case "125":
								sch[_e[132]] = 669;
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					if (numcamaras == 5)
					{

						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 508;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variável
								break;
							case "115":
								sch[_e[116]] = 751;
								break;
							case "211":
								sch[_e[212]] = 669;
								break;
							case "213":
								sch[_e[214]] = tempocamaras; //variável
								break;
							case "215":
								sch[_e[216]] = 751;
								break;
							case "311":
								sch[_e[312]] = 669;
								break;
							case "313":
								sch[_e[314]] = tempocamaras; //variável
								break;
							case "315":
								sch[_e[316]] = 669;
								break;
							case "221":
								sch[_e[222]] = 751;
								break;
							case "223":
								sch[_e[224]] = tempocamaras; //variável
								break;
							case "225":
								sch[_e[226]] = 669;
								break;
							case "121":
								sch[_e[122]] = 751;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variável
								break;
							case "125":
								sch[_e[132]] = 669;
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					if (numcamaras == 6)
					{

						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 508;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variável
								break;
							case "115":
								sch[_e[116]] = 751;
								break;
							case "211":
								sch[_e[212]] = 669;
								break;
							case "213":
								sch[_e[214]] = tempocamaras; //variável
								break;
							case "215":
								sch[_e[216]] = 751;
								break;
							case "311":
								sch[_e[312]] = 669;
								break;
							case "313":
								sch[_e[314]] = tempocamaras; //variável
								break;
							case "315":
								sch[_e[322]] = 832;
								break;
							case "323":
								sch[_e[324]] = tempocamaras; //variável
								break;
							case "325":
								sch[_e[326]] = 669;
								break;
							case "221":
								sch[_e[222]] = 751;
								break;
							case "223":
								sch[_e[224]] = tempocamaras; //variável
								break;
							case "225":
								sch[_e[226]] = 669;
								break;
							case "121":
								sch[_e[122]] = 751;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variável
								break;
							case "125":
								sch[_e[132]] = 669;
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					if (numcamaras == 7)
					{

						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 508;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variável
								break;
							case "115":
								sch[_e[116]] = 751;
								break;
							case "211":
								sch[_e[212]] = 669;
								break;
							case "213":
								sch[_e[214]] = tempocamaras; //variável
								break;
							case "215":
								sch[_e[216]] = 751;
								break;
							case "311":
								sch[_e[312]] = 669;
								break;
							case "313":
								sch[_e[314]] = tempocamaras; //variável
								break;
							case "315":
								sch[_e[316]] = 751;
								break;
							case "411":
								sch[_e[412]] = 669;
								break;
							case "413":
								sch[_e[414]] = tempocamaras; //variável
								break;
							case "415":
								sch[_e[426]] = 669;
								break;
							case "321":
								sch[_e[322]] = 751;
								break;
							case "323":
								sch[_e[324]] = tempocamaras; //variável
								break;
							case "325":
								sch[_e[326]] = 669;
								break;
							case "221":
								sch[_e[222]] = 751;
								break;
							case "223":
								sch[_e[224]] = tempocamaras; //variável
								break;
							case "225":
								sch[_e[226]] = 669;
								break;
							case "121":
								sch[_e[122]] = 751;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variável
								break;
							case "125":
								sch[_e[132]] = 669;
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					break;

				case 3: //caso seja layout linear com E/S separado

					if (numcamaras == 4)
					{
						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 508;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variável
								break;
							case "115":
								sch[_e[122]] = 832;
								break;
							case "211":
								sch[_e[212]] = 669;
								break;
							case "213":
								sch[_e[214]] = tempocamaras; //variável
								break;
							case "215":
								sch[_e[222]] = 832;
								break;
							case "223":
								sch[_e[224]] = tempocamaras; //variável
								break;
							case "225":
								sch[_e[226]] = 751;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variável
								break;
							case "125":
								sch[_e[126]] = 751;
								break;
							case "23":
								sch[_e[24]] = 706;
								break;
						}
					}

					if (numcamaras == 5)
					{
						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 508;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variável
								break;
							case "115":
								sch[_e[122]] = 832;
								break;
							case "211":
								sch[_e[212]] = 669;
								break;
							case "213":
								sch[_e[214]] = tempocamaras; //variável
								break;
							case "215":
								sch[_e[222]] = 832;
								break;
							case "223":
								sch[_e[224]] = tempocamaras; //variável
								break;
							case "225":
								sch[_e[226]] = 751;
								break;
							case "311":
								sch[_e[312]] = 669;
								break;
							case "313":
								sch[_e[314]] = tempocamaras; //variável
								break;
							case "315":
								sch[_e[316]] = 751;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variável
								break;
							case "125":
								sch[_e[126]] = 751;
								break;
							case "23":
								sch[_e[24]] = 706;
								break;
						}
					}

					if (numcamaras == 6)
					{
						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 508;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variável
								break;
							case "115":
								sch[_e[122]] = 832;
								break;
							case "211":
								sch[_e[212]] = 669;
								break;
							case "213":
								sch[_e[214]] = tempocamaras; //variável
								break;
							case "215":
								sch[_e[222]] = 832;
								break;
							case "223":
								sch[_e[224]] = tempocamaras; //variável
								break;
							case "225":
								sch[_e[226]] = 751;
								break;
							case "311":
								sch[_e[312]] = 669;
								break;
							case "313":
								sch[_e[314]] = tempocamaras; //variável
								break;
							case "315":
								sch[_e[322]] = 832;
								break;
							case "323":
								sch[_e[324]] = tempocamaras; //variável
								break;
							case "325":
								sch[_e[326]] = 751;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variável
								break;
							case "125":
								sch[_e[126]] = 751;
								break;
							case "23":
								sch[_e[24]] = 706;
								break;
						}
					}

					if (numcamaras == 7)
					{
						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 508;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variável
								break;
							case "115":
								sch[_e[122]] = 832;
								break;
							case "211":
								sch[_e[212]] = 669;
								break;
							case "213":
								sch[_e[214]] = tempocamaras; //variável
								break;
							case "215":
								sch[_e[222]] = 832;
								break;
							case "223":
								sch[_e[224]] = tempocamaras; //variável
								break;
							case "225":
								sch[_e[226]] = 751;
								break;
							case "311":
								sch[_e[312]] = 669;
								break;
							case "313":
								sch[_e[314]] = tempocamaras; //variável
								break;
							case "315":
								sch[_e[322]] = 832;
								break;
							case "323":
								sch[_e[324]] = tempocamaras; //variável
								break;
							case "325":
								sch[_e[326]] = 751;
								break;
							case "411":
								sch[_e[412]] = 669;
								break;
							case "413":
								sch[_e[414]] = tempocamaras; //variável
								break;
							case "415":
								sch[_e[426]] = 751;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variável
								break;
							case "125":
								sch[_e[126]] = 751;
								break;
							case "23":
								sch[_e[24]] = 706;
								break;
						}
					}

					break;

				case 4: //caso seja layout radial com 2 robos

					if (numcamaras == 4)
					{

						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 474;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variavel
								break;
							case "115":
								sch[_e[122]] = 739;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variavel
								break;
							case "125":
								sch[_e[132]] = 781;
								break;
							case "133":
								sch[_e[134]] = tempocamaras; //variavel
								break;
							case "135":
								sch[_e[142]] = 672;
								break;
							case "143":
								sch[_e[144]] = tempocamaras; //variavel
								break;
							case "145":
								sch[_e[152]] = 690;
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					if (numcamaras == 5)
					{

						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 454;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variavel
								break;
							case "115":
								sch[_e[122]] = 700;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variavel
								break;
							case "125":
								sch[_e[132]] = 741;
								break;
							case "133":
								sch[_e[134]] = tempocamaras; //variavel
								break;
							case "135":
								sch[_e[142]] = 768;
								break;
							case "143":
								sch[_e[144]] = tempocamaras; //variavel
								break;
							case "145":
								sch[_e[152]] = 741;
								break;
							case "153":
								sch[_e[154]] = tempocamaras; //variavel
								break;
							case "155":
								sch[_e[162]] = 669;
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					if (numcamaras == 6)
					{

						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 454;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variavel
								break;
							case "115":
								sch[_e[122]] = 700;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variavel
								break;
							case "125":
								sch[_e[132]] = 741;
								break;
							case "133":
								sch[_e[134]] = tempocamaras; //variavel
								break;
							case "135":
								sch[_e[142]] = 768;
								break;
							case "143":
								sch[_e[144]] = tempocamaras; //variavel
								break;
							case "145":
								sch[_e[152]] = 741;
								break;
							case "153":
								sch[_e[154]] = tempocamaras; //variavel
								break;
							case "155":
								sch[_e[162]] = 700;
								break;
							case "163":
								sch[_e[164]] = tempocamaras; //variavel
								break;
							case "165":
								sch[_e[172]] = 596;
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					if (numcamaras == 7)
					{
						switch (ev.ToString())
						{
							case "11":
								sch[_e[12]] = 535;
								break;
							case "103":
								sch[_e[112]] = 454;
								break;
							case "113":
								sch[_e[114]] = tempocamaras; //variavel
								break;
							case "115":
								sch[_e[122]] = 700;
								break;
							case "123":
								sch[_e[124]] = tempocamaras; //variavel
								break;
							case "125":
								sch[_e[126]] = 692;
								break;
							case "211":
								sch[_e[212]] = 623;
								break;
							case "213":
								sch[_e[214]] = tempocamaras; //variavel
								break;
							case "215":
								sch[_e[222]] = 739;
								break;
							case "223":
								sch[_e[224]] = tempocamaras; //variavel
								break;
							case "225":
								sch[_e[232]] = 672;
								break;
							case "233":
								sch[_e[234]] = tempocamaras; //variavel
								break;
							case "235":
								sch[_e[246]] = 761;
								break;
							case "131":
								sch[_e[132]] = 596;
								break;
							case "133":
								sch[_e[134]] = tempocamaras; //variavel
								break;
							case "135":
								sch[_e[142]] = 700;
								break;
							case "143":
								sch[_e[144]] = tempocamaras; //variavel
								break;
							case "145":
								sch[_e[152]] = 692; //variavel
								break;
							case "13":
								sch[_e[14]] = 706;
								break;
						}
					}

					break;
			}
			return sch;
		};
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
