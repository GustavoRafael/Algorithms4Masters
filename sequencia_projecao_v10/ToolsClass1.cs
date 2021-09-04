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

using sequencia_projecao_v10;

namespace sequencia_projecao_v10
{
    class ToolsClass
    {
        public void ShowResultado(List<(double time, AbstractEvent[] sequency, AbstractState[] dvstate)> indSel)
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

        public void ReadFileSeqTimed(ISchedulingProblem plant, string fileName, int product)
        {
            sequencia_projecao_v10.ClassMXP mp = new ClassMXP();
            sequencia_projecao_v10.CLONALClass clonalMet = new CLONALClass();

            var transit = plant.Supervisor
                .Transitions.AsParallel()
                .GroupBy(t => t.Origin)
                .ToDictionary(gr => gr.Key, gr => gr.ToArray());

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

            var divStates = clonalMet.TimeDivStatesEvaluation(plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                llSeq.ToArray(),
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(product),
                transit
                );
            var avlObj = clonalMet.AvaliaObjetivo(
                llSeq.ToArray().Where(e1 => e1.IsControllable).ToArray(),
                plant.InitialScheduler,
                plant.InitialRestrition(product),
                plant.UpdateFunction,
                plant.InitialState,
                transit,
                divStates.dvstate);

            var paral = mp.ParallelismEvaluation(
                plant.Supervisor,
                plant.InitialState,
                plant.InitialState,
                llSeq.ToArray(),
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(product),
                transit
                );
            var paralGU = mp.ParallelismEvaluation(
                plant.Supervisor,
                plant.InitialState,
                plant.InitialState,
                avlObj.sequency,
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(product),
                transit
                );

            var tempo = mp.TimeEvaluation(
                plant.Supervisor,
                plant.InitialState,
                plant.TargetState,
                llSeq.ToArray(),
                plant.InitialScheduler,
                plant.UpdateFunction,
                plant.InitialRestrition(product),
                transit
                );

            var seqTam = llSeq.ToArray().Count();
            Console.Write("\n A sequencia do arquivo ( {0} ) possui o \ntempo de {1}, \nTG {2}, \nparalelismo {3}, \nparal GU {4} \nnum divStates {5} \ndivTime{6}, \n tam:{7}", fileName, tempo, avlObj.time, paral, paralGU, divStates.dvstate.Count(),divStates.time, seqTam);
        }

        public void WriteFileSeqTimed(double[] evTime, AbstractEvent[][] events, string fileName)
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

        public void SaveData(List<double> value2save, string fileName)
        {
            // salva no diretório escolhido
            System.Threading.Thread.CurrentThread.CurrentCulture = new System.Globalization.CultureInfo("en-US");
            var file_name = fileName;                            
            using (var file = File.CreateText(file_name + ".txt"))
            {
                foreach (var ev in value2save)
                {
                    file.Write(ev.ToString());
                    file.Write(',');                                  
                }
            }
        }

        public void SaveDataOf2Variable(List<double> value2save1, List<double> value2save2, string fileName)
        {
            // salva no diretório escolhido
            System.Threading.Thread.CurrentThread.CurrentCulture = new System.Globalization.CultureInfo("en-US");
            var file_name = fileName;
            using (var file = File.CreateText(file_name + ".txt"))
            {
                foreach (var ev1 in value2save1)
                {
                    file.Write(ev1.ToString());
                    file.Write(',');
                }
                file.Write('\n');
                foreach (var ev2 in value2save2)
                {
                    file.Write(ev2.ToString());
                    file.Write(',');
                }
            }
        }

        public void WriteDataFile2(List<(double numProdc, string source, double time, double iter, double nGeracoes,
            double MakespamMin, double MakespamMed, double MakespamSTD, double MakespamMAX)> dataFile, string fileName)
        {
            // salva no diretório escolhido
            System.Threading.Thread.CurrentThread.CurrentCulture = new System.Globalization.CultureInfo("en-US");
            var file_name = fileName + "_teste.csv";  //fileName + "_SFM_" + numProd.ToString() + "A_B.csv";                            // rept.ToString() +"_SFM_8A_8B_sequency_data.csv";
            using (var file = File.CreateText(file_name))
            {
                foreach (var df in dataFile)
                {
                    file.Write(df.numProdc);
                    file.Write(',');
                    file.Write(df.source);
                    file.Write(',');
                    file.Write(df.MakespamMin);
                    file.Write(',');
                    file.Write(df.MakespamMed);
                    file.Write(',');
                    file.Write(df.MakespamSTD);
                    file.Write(',');
                    file.Write(df.iter);
                    file.Write(',');
                    file.Write(df.nGeracoes);
                    file.Write(',');
                    file.Write(df.MakespamMAX);
                    file.Write(',');
                    file.Write(df.time);
                    file.Write('\n');
                }
            }
        }

        // contador de tempo do lucaas
        public float TimeEval(DFA S, AbstractState initial, AbstractState destination,
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
    }


    // salva a melhor sequencia
    //tools.WriteFileSeqTimed(bestMsp,bestSeq, np.ToString() + "ITL_bestSeq_03.txt");

    // para salvar em arquivo
    /*
    dataSave.Add((
        np,
        sc,
        Math.Round((data.Select(ck => ck.time).Sum())/60000,3),
        Math.Round(data.Select(ni => ni.iter).Average(),2),
        Math.Round(data.Select(ng => ng.nGeracoes).Average(),2),
        data.Select(mk => mk.medMakespam).Min(),
        Math.Round(data.Select(mk => mk.medMakespam).Average(), 2),
        Math.Round((data.Select(mk => mk.medMakespam).ToList()).StandardDeviation(), 2),
        data.Select(mk => mk.medMakespam).Max()
        ));
        */
}
