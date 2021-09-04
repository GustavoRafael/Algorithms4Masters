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
    class CLONALClass
    {
        private static readonly MyRandom Rnd = new MyRandom();

        // GU: Algoritmo de seleção clonal
        public ((double time, AbstractEvent[] sequency, AbstractState[] dvState)[], int numAvalfobj, int numeroTotalGeracoes) CLONAL(
            ISchedulingProblem p1,
            int prodA,
            Dictionary<AbstractState, Transition[]> transicoes,
            double pbtState,
            int indPolulacao = 20,
            int numIndMutados = 10,
            int numMaxGeracoes = 10,
            int SelecIndGeracao = 2,
            int numGeracaoSemMelhorasMax = 30,
            string source = "randInd",
            double percentMix = 0.2,    // percentual de mistura (DS method and MP methods)
            double percDSpreserved = 1.0
           )
        {
            sequencia_projecao_v10.ClassMXP mxp = new ClassMXP();
            sequencia_projecao_v10.ToolsClass toolsDataSave = new ToolsClass();
            sequencia_projecao_v10.FLPClass ghCSA = new FLPClass();

            //var timer = new Stopwatch();
            //timer.Start();

            var numAvalfObj = 0;
            var jaAvaliados = new HashSet<(double time, AbstractEvent[] sequency, AbstractState[] dvstate)>();

            var individuosAleatorios = new List<(double time, AbstractEvent[] sequency, AbstractState[] dvstate)>();
            var divZero = new List<AbstractState>().ToArray();
            switch (source) // source of the individuals in the optimization (from pure DS method, or mixed with Maximum Paralleslism methods (TMP,HSM,LMP)) 
            {
                case "randInd":
                    // valor default indPopulacao = 10
                    individuosAleatorios = Enumerable.Range(0, 5 * indPolulacao)
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
                            .Select(i => mxp.LogicalMaximumParallelism(
                                p1.Supervisor,
                                p1.InitialState,
                                p1.Depth * prodA,
                                p1.TargetState,
                                p1.InitialRestrition(prodA),
                                transicoes));
                    foreach (var idv in seqs)
                    {
                        individuosAleatorios.Add((
                            0.0,
                            idv.Where(lp => lp.IsControllable).ToArray(),
                            divZero));
                    }
                    break;

                case "mixRandLMP":
                    var halfSeqLMP = Enumerable.Range(0, Convert.ToInt32(indPolulacao * percentMix))
                        .AsParallel()
                        .Select(i => mxp.TimedMaximumParallelism(
                            p1.Supervisor,
                            p1.InitialState,
                            p1.TargetState,
                            p1.Depth * prodA,
                            p1.InitialScheduler,
                            p1.UpdateFunction,
                            p1.InitialRestrition(prodA),
                            transicoes
                        ));

                    var halfSeqRandLMP = Enumerable.Range(0, Convert.ToInt32(indPolulacao *(1.0 - percentMix)))
                        .AsParallel()
                        .Select(i => SequenciaAleatoria(
                            p1.Depth * (prodA),
                            p1.InitialScheduler,
                            p1.InitialRestrition(prodA),
                            p1.InitialState,
                            p1.TargetState,
                            transicoes).sequency.AsEnumerable());

                    foreach (var idv in halfSeqLMP.Union(halfSeqRandLMP))
                    {
                        individuosAleatorios.Add((
                            0.0,
                            idv.Where(lp => lp.IsControllable).ToArray(),
                            divZero));
                    }
                    break;

                case "mixRandMfe": // Most frequent event

                    var halfSeqMfe = Enumerable.Range(0, Convert.ToInt32(indPolulacao * percentMix))                   //  gera um conjunto n de soluções
                        .AsParallel()
                        .Select(i => ghCSA.FullProductionLine(
                            p1.Depth * (prodA),
                            p1.InitialScheduler,
                            p1.InitialRestrition(prodA),
                            p1.UpdateFunction,
                            p1.InitialState,
                            p1.TargetState,
                            transicoes
                         )).Select(sol => sol.sequency);

                    var halfSeqRand = Enumerable.Range(0, Convert.ToInt32(indPolulacao * (1.0 - percentMix)))
                        .AsParallel()
                        .Select(i => SequenciaAleatoria(
                            p1.Depth * (prodA),
                            p1.InitialScheduler,
                            p1.InitialRestrition(prodA),
                            p1.InitialState,
                            p1.TargetState,
                            transicoes).sequency.AsEnumerable());

                    foreach (var idv in halfSeqMfe.Union(halfSeqRand))
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
                        .Select(i => mxp.TimedMaximumParallelism(
                            p1.Supervisor,
                            p1.InitialState,
                            p1.TargetState,
                            p1.Depth * prodA,
                            p1.InitialScheduler,
                            p1.UpdateFunction,
                            p1.InitialRestrition(prodA),
                            transicoes
                        ));
                    foreach (var idv in seqsTMP)
                    {
                        individuosAleatorios.Add((
                            0.0,
                            idv.Where(lp => lp.IsControllable).ToArray(),
                            divZero));
                    }
                    break;

                case "mixRandTMP":
                    var halfSeqTMP = Enumerable.Range(0, Convert.ToInt32(indPolulacao * percentMix))
                        .AsParallel()
                        .Select(i => mxp.TimedMaximumParallelism(
                            p1.Supervisor,
                            p1.InitialState,
                            p1.TargetState,
                            p1.Depth * prodA,
                            p1.InitialScheduler,
                            p1.UpdateFunction,
                            p1.InitialRestrition(prodA),
                            transicoes
                        ));
                    
                    var halfSeqRandTMP = Enumerable.Range(0, Convert.ToInt32(indPolulacao *(1.0 - percentMix)))
                        .AsParallel()
                        .Select(i => SequenciaAleatoria(
                            p1.Depth * (prodA),
                            p1.InitialScheduler,
                            p1.InitialRestrition(prodA),
                            p1.InitialState,
                            p1.TargetState,
                            transicoes).sequency.AsEnumerable());

                    foreach (var idv in halfSeqTMP.Union(halfSeqRandTMP))
                    {
                        individuosAleatorios.Add((
                            0.0,
                            idv.Where(lp => lp.IsControllable).ToArray(),
                            divZero));
                    }
                    break;

                case "HSM":
                    var seqsHMP = Enumerable.Range(0, 2 * indPolulacao)
                        .AsParallel()
                        .Select(i => mxp.HeuristicShortestMakespan(
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

                case "mixRandHSM":
                    var halfSeqHSM = Enumerable.Range(0, Convert.ToInt32(indPolulacao * percentMix))
                        .AsParallel()
                        .Select(i => mxp.HeuristicShortestMakespan(
                            p1.Supervisor,
                            p1.InitialState,
                            p1.TargetState,
                            p1.Depth * prodA,
                            p1.InitialScheduler,
                            p1.UpdateFunction,
                            p1.InitialRestrition(prodA),
                            transicoes
                        ));


                    var halfSeqRandHSM = Enumerable.Range(0, Convert.ToInt32(indPolulacao * (1.0 - percentMix)))
                        .AsParallel()
                        .Select(i => SequenciaAleatoria(
                            p1.Depth * (prodA),
                            p1.InitialScheduler,
                            p1.InitialRestrition(prodA),
                            p1.InitialState,
                            p1.TargetState,
                            transicoes).sequency.AsEnumerable());

                    foreach (var idv in halfSeqHSM.Union(halfSeqRandHSM))
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
                .Where(s1 => s1.time != 1234 && s1.sequency.Count() == p1.Depth*prodA)              // garante q não ha erro no tempo e que a sequencia tenha tamanho certo
                .OrderBy(seq => seq.time)
                .Take(indPolulacao)
                //.Take(Convert.ToInt32(individuosAleatorios.Count() * 0.50))
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
            var bestSol = new List<(double time, AbstractEvent[] sequency, AbstractState[] dvstate)>();
            bestSol = indSelecionados.OrderBy(st => st.time).Take(1).ToList();                  // salva a primeira melhor solução

            // dados para avaliar a melhora do algoritmo
            var convergenceData = new[] {0.0}.ToList();
           

            while (numGeracaoSemMelhoras < numGeracaoSemMelhorasMax && numeroTotalGeracoes < numMaxGeracoes)
            {
                //  valor medio do makespan por geração da população              
                //convergenceData.Add(indSelecionados.Select(ind=> ind.time).Average());

                // GU-11/02/2018:  
                var numIntervalo = indSelecionados.Count;
                var taxaReduxIndivMutados = 1.0 / numIntervalo;//Math.Round(1.00/numIntervalo,2);
                var taxaReduxDS = 1.0 / numIntervalo;//Math.Round(1.00/numIntervalo,2);
                Double acumulaPercIndMutatos = 0.0;
                Double acumulaReduxDS = 0.0;
                acumulaPercIndMutatos = acumulaPercIndMutatos + taxaReduxIndivMutados;
                acumulaReduxDS = acumulaReduxDS + taxaReduxDS;

                foreach (var sInd in indSelecionados)
                {
                    // evita availar individuos repetidos
                    if (!jaAvaliados.Contains(sInd))
                    {
                        jaAvaliados.Add(sInd);
                       
                        var ppseq = percDSpreserved - acumulaReduxDS;

                        var pcIndMut = 1.0 - acumulaPercIndMutatos < 0.01 ? 0.01 : 1.0 - acumulaPercIndMutatos;
                        // GU: Gera novos indivíduos filhos (de acordo com o numInividuos), a partir de uma sequencia pai sInd
                        // valor default numIndividuosMutados = 5;
                        novosIndividuos = Enumerable.Range(0, Convert.ToInt32((Math.Round(pcIndMut, 2)) * numIndMutados))  // gera indivíduos proporcional ao rank da sua solução (1º tem mais filhos os ultimo tem menos)
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
                                Math.Round(ppseq < 0.0 ? 0.0 : ppseq, 2)                    // percentusal preservado da sequência
                                ))
                                .Where(se => se.time != 1234)
                                //.OrderBy(seq => seq.time)
                                //.Take(SelecIndGeracao)                                      // são selecionados os N primeiros indivívduos (N = numero de indivíduos)
                                .ToList();

                        numAvalfObj += novosIndividuos.Count();

                        // adiciona o pai
                        novosIndividuos.Add(sInd);
                        //GU: adiciona os melhores individuos a conjuntos das soluções não dominadas e pega os 80% m
                        //GU: 05/fev/2018 - a partir de sugestão da professora serão selecionados os melhores filhos e adicionados ao conjunto de soluções  
                        novaGeracao = novaGeracao.Union(novosIndividuos.OrderBy(seq => seq.time).Take(SelecIndGeracao)).ToList();

                        // atualiza o qto de modificação o proximo individuo vai sofrer
                        acumulaPercIndMutatos = acumulaPercIndMutatos + taxaReduxIndivMutados;
                        acumulaReduxDS = acumulaReduxDS + taxaReduxDS;
                    }
                    else
                    {
                        if (sInd.time <= menorMakespanAtual)
                        {
                            menorMakespanAtual = sInd.time;
                            numAvalfObj += 1;
                            novaGeracao.Add(sInd); //novaGeracao.Union(sInd).ToList();
                        }
                        acumulaPercIndMutatos = acumulaPercIndMutatos + taxaReduxIndivMutados;
                        acumulaReduxDS = acumulaReduxDS + taxaReduxDS;
                        continue;
                    }
                }
                //GU: 05/02/2018 - Avalia se houve melhora ou não
                menorMakespamMedido = (novaGeracao.Count() == 0 ? menorMakespanAtual + 10 : novaGeracao.Select(msp => msp.time).Min());
                if (menorMakespamMedido < menorMakespanAtual)
                {
                    menorMakespanAtual = menorMakespamMedido;
                    numGeracaoSemMelhoras = 0;
                    ++numeroTotalGeracoes;
                    bestSol = bestSol.Union(novaGeracao.OrderBy(s => s.time).Take(1)).ToList();
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
            
            // valor medio do makespan por geração da população final           
            //convergenceData.Add(indSelecionados.Select(ind => ind.time).Average());     //.OrderBy(st => st.time).First().time);//
            //toolsDataSave.SaveData(convergenceData, "_dados_da_conversão_clusterTool_R2_25P_"+ (percentMix*100).ToString() + ((1-percentMix)*100).ToString()+"_mixRandTMP");
            //toolsDataSave.SaveData(convergenceData, "_dados_da_conversão_SFM_5P_" + (percentMix * 100).ToString() +"_"+ ((1 - percentMix) * 100).ToString() + "_mixRandTMP");
            //toolsDataSave.SaveData(convergenceData, "_dados_da_conversão_SFM_5P_"+"_randInd");

            // termina mutaGen
            indSelecionados = bestSol.OrderBy(seq => seq.time)
                .Take(indPolulacao)
                .ToList();

            return (indSelecionados.ToArray(), numAvalfObj, numeroTotalGeracoes);
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
                    
                    if (trans.Count > 1 && trans.Where(tr => tr.IsControllableTransition).Count() > 1 && selectDivStates.Contains(estado))            // mudanca dia 04/10/2018  trans.All(tr => tr.IsControllableTransition)
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
                if (trans.Count > 1 && trans.Where(tr => tr.IsControllableTransition).Count() > 1)
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
            return (tempo, newSeq.ToArray(), newDivState.ToArray());
        }

        // GU: gera sequências aleatórias (indivíduos)
        public (double time, AbstractEvent[] sequency, AbstractState[] dvstate) SequenciaAleatoria(
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
                if (trans.Any(ts => ts.IsControllableTransition && schSA[ts.Trigger] > 0))
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

                    var tmin = transitions[estado].Where(t => !t.IsControllableTransition).Select(t => schSA[t.Trigger]).Min();
                    trans = transitions[estado].Where(t => !t.IsControllableTransition && schSA[t.Trigger] == tmin).ToList();
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

            return (tempo, seq.Where(e => e.IsControllable).ToArray(), dstate.ToArray());
        }

        // GU: calcula o makespan da sequencia passada (de um indivíduo)- comprar com a outra que conta o tempo
        public (double time, AbstractEvent[] sequency, AbstractState[] dvstate) AvaliaObjetivo(
            AbstractEvent[] ncseqProj,
            Scheduler schAV,
            Restriction resAV,
            Update update,
            AbstractState inicial,
            Dictionary<AbstractState, Transition[]> transitions,
            AbstractState[] dvstate
            )
        {
            double tempo = 0;
            var seqAval = new List<AbstractEvent>();
            var estado = inicial;
            var seqProj = ncseqProj.Select(t => t).Where(e => e.IsControllable).ToArray();
            var newDvstate = new List<AbstractState>();

            for (var k = 0; k < seqProj.Length; k++)
            {
                var trans = transitions[estado].Where(t => t.IsControllableTransition && resAV[t.Trigger] > 0).ToList();
                var transAV = transitions[estado].Where(t => !t.IsControllableTransition).ToList();

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

                    var tminAV = transitions[estado].Where(t => !t.IsControllableTransition).Select(t2 => schAV[t2.Trigger]).Min();
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
                var tmin = transitions[estado].Where(t => !t.IsControllableTransition).Select(t => schAV[t.Trigger]).Min();
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
        public (double time, AbstractEvent[] sequency, AbstractState[] dvstate) TimeDivStatesEvaluation(
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
                    if (trans.Count() > 1 && trans.Where(tr => tr.IsControllableTransition).Count() > 1 && e.IsControllable == true)
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

    }
}
