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
    class greedy_search
    {
        private static readonly MyRandom Rndgreedy = new MyRandom(); // gerador de numeros aleatorios

        // com base nos caminhos possivei a partir do DS state seleciondado, são gerados os novos filhos
        private static List <(double makespan, AbstractEvent[] sequency, AbstractState[] dvstate )> dsoffspring (
            AbstractState dsInvestigated,
            int depth,
            AbstractEvent[] seqProj,
            Scheduler schMG,
            Restriction resMG,
            Update update,
            AbstractState inicial,
            AbstractState target,
            Dictionary<AbstractState, Transition[]> transitions,
            AbstractState[] dvState,
            double pcpreserveSeq = 0.8              // qdo criada todos os individuos tinha valores fixos. Agora são aleatórios
            )
        {
            // variaveis iniciais para o recalculo dos os filhos
            double tempo = 0;
            var newSeq = new List<AbstractEvent>();
            var estado_atual = inicial;
            var seqOriginal = seqProj.ToList();
            var evento = seqOriginal.First();
            var evento_atual = 0;

            var parentDivStates = dvState.Take(Convert.ToInt32(dvState.Count() * pcpreserveSeq)).ToList();
            var offspringDivState = new List<AbstractState>();

            var offspring = new List<(double mks, AbstractEvent[] seqcy, AbstractState[] dvste)>(); // armazena os filhos encontrados 

            // repete a sequencia ate o ponto em serão criados os filhos
            while (parentDivStates.First() != dsInvestigated) // aguardando q o ds atual se torno ds a ser investigado
            {
                var trans = transitions[estado_atual].Where(t => t.IsControllableTransition && resMG[t.Trigger] > 0).ToList();

                // trata os eventos controlaveis
                if (trans.Any(t => t.Trigger.IsControllable && t.Trigger == seqProj[evento_atual]))
                {
                    // armazena os estado_atuals divergentes

                    if (trans.Count > 1 && trans.Where(tr => tr.IsControllableTransition).Count() > 1 && parentDivStates.Contains(estado_atual))            // mudanca dia 04/10/2018  trans.All(tr => tr.IsControllableTransition)
                    {
                        offspringDivState.Add(estado_atual);
                        parentDivStates.Remove(estado_atual);
                    }

                    newSeq.Add(seqProj[evento_atual]);

                    if (seqProj[evento_atual].IsControllable) resMG[seqProj[evento_atual]]--;  // res[e] --  reduz a quantidade eventos relativa ao numero de produtos.
                    // atualiza os dados temporais
                    tempo += schMG[seqProj[evento_atual]];
                    schMG = update(schMG, seqProj[evento_atual]);

                    estado_atual = trans.Single(t => t.Trigger == seqProj[evento_atual]).Destination;
                }
                else // trata os eventos não controláveis 
                {
                    trans = transitions[estado_atual].Where(t => !t.IsControllableTransition && t.Trigger == seqProj[evento_atual]).ToList();

                    estado_atual = trans.Single(t => t.Trigger == seqProj[evento_atual]).Destination;

                    newSeq.Add(seqProj[evento_atual]);
                    tempo += schMG[seqProj[evento_atual]];
                    schMG = update(schMG, seqProj[evento_atual]);
                }

                evento_atual++; // incrementa para o proximo evento na lista
            }
            var newDepth = newSeq.Count();

            // qdo o estado investigado é alcançado 
            estado_atual = dsInvestigated;
            

            // variaveis temporarias para geração das sequencias filhas

            var temp_newDepth = newDepth;
            var temp_tempo = tempo;
            var temp_schMG = schMG;
            var temp_offspringDivState = offspringDivState;
            var temp_newSeq = newSeq;
            var temp_estado_atual = estado_atual;
            var temp_resMG = resMG;

            // as transições com os eventos possiveis - assumindo q toda vez q chegar nesse ponto o estado seja divergente
            var offspringgeneration = transitions[estado_atual].Where(t => t.IsControllableTransition ).Select(ep => ep.Trigger).ToList();


            // geração dos filhos a partir do eventos possiveis
            foreach (var evpossiveis in offspringgeneration)
            {
                // Variaveis temporárias - armazenão a condição inicial para q todos os filhos possam partir do mesmo ponto
                newDepth = temp_newDepth;
                tempo = temp_tempo;
                schMG = temp_schMG;
                offspringDivState = temp_offspringDivState;
                newSeq = temp_newSeq;
                estado_atual = temp_estado_atual;
                resMG = temp_resMG;

                // Mutação no resto da sequencia
                Transition transicao;
                for (var k = newDepth; k < depth; k++) // respeitar o tamanho da sequencia 
                {
                    var trans = transitions[estado_atual].Where(t => t.IsControllableTransition && resMG[t.Trigger] > 0).ToList();
                    //var trans2 = transitions[estado_atual].Where(t => !t.IsControllableTransition).ToList();

                    // qdo eventos controláveis modificam o tempo SFM 61,63,65
                    if (trans.Any(ts => ts.IsControllableTransition && schMG[ts.Trigger] > 0 && resMG[ts.Trigger] > 0))
                    {

                        var tminAV = transitions[estado_atual]
                            .Where(t => t.IsControllableTransition && resMG[t.Trigger] > 0 && schMG[t.Trigger] > 0 || !t.IsControllableTransition)
                            .Select(t2 => schMG[t2.Trigger])
                            .Min();
                        var transicao1 = transitions[estado_atual].First(t => schMG[t.Trigger] == tminAV);

                        tempo += schMG[transicao1.Trigger];

                        schMG = update(schMG, transicao1.Trigger);
                        newSeq.Add(transicao1.Trigger);
                        estado_atual = transicao1.Destination;

                        if (transicao1.Trigger.IsControllable) resMG[transicao1.Trigger]--;

                        continue;
                    }

                    // qdo não houver evento c ou nc pra ocorrer
                    if (transitions[estado_atual].Where(tw => tw.IsControllableTransition && resMG[tw.Trigger] > 0 || !tw.IsControllableTransition).Count() == 0)
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
                        var tminMG = transitions[estado_atual].Where(t => !t.IsControllableTransition).Select(t => schMG[t.Trigger]).Min();
                        trans = transitions[estado_atual].Where(t => !t.IsControllableTransition && schMG[t.Trigger] == tminMG).ToList();

                        transicao = trans.Random(Rndgreedy);

                        tempo += schMG[transicao.Trigger];

                        schMG = update(schMG, transicao.Trigger);
                        newSeq.Add(transicao.Trigger);
                        estado_atual = transicao.Destination;

                        continue;
                    }

                    // realiza a escolha do caminho, hora baseada no evento escolhido, ora de forma aleatória
                    // 
                    if (temp_estado_atual == estado_atual & temp_newDepth == k) // garantir q apenas uma vez por evento possivel se visite essa condiçã0
                    {
                        // faz o evento selecionado
                        offspringDivState.Add(estado_atual);

                        // seleciona de acordo com o evento possivel                                                   

                        if (evpossiveis.IsControllable) resMG[evpossiveis]--;

                        tempo += schMG[evpossiveis];

                        schMG = update(schMG, evpossiveis);
                        newSeq.Add(evpossiveis);
                        estado_atual = transitions[estado_atual].Where(ts => ts.Trigger == evpossiveis).Select(upstate => upstate.Destination).First(); // atualiza o estafo atual
                    }
                    else
                    {   
                        // geração aleatoria do resto do caminho
                        // armazena os novos estado_atuals divergentes
                        if (trans.Count > 1 && trans.Where(tr => tr.IsControllableTransition).Count() > 1)
                        {
                            offspringDivState.Add(estado_atual);

                            transicao = trans.Random(Rndgreedy); // seleciona aleatoriamente o proximo evento  

                            if (transicao.Trigger.IsControllable) resMG[transicao.Trigger]--;

                            tempo += schMG[transicao.Trigger];

                            schMG = update(schMG, transicao.Trigger);
                            newSeq.Add(transicao.Trigger);
                            estado_atual = transicao.Destination;
                        }
                        else if (trans.Count == 1 && resMG[trans.Select(te => te.Trigger).First()] > 0)
                        {
                            transicao = trans.First();
                            if (transicao.Trigger.IsControllable) resMG[transicao.Trigger]--;

                            tempo += schMG[transicao.Trigger];

                            schMG = update(schMG, transicao.Trigger);
                            newSeq.Add(transicao.Trigger);
                            estado_atual = transicao.Destination;
                        }
                        else
                        {
                            k--;
                        }
                    }
                }

                // completa os eventos nao controláveis q ainda existem apos o fim do while
                while (schMG.Select(ind => !ind.Key.IsControllable && !float.IsInfinity(ind.Value)).Any(s => s))
                {
                    var tmin = transitions[estado_atual].Where(t => !t.IsControllableTransition).Select(t => schMG[t.Trigger]).Min();
                    var transicao1 = transitions[estado_atual].First(t => !t.IsControllableTransition && schMG[t.Trigger] == tmin);

                    tempo += schMG[transicao1.Trigger];

                    schMG = update(schMG, transicao1.Trigger);
                    newSeq.Add(transicao1.Trigger);
                    estado_atual = transicao1.Destination;
                }

                if (estado_atual != inicial)
                {
                    tempo = 1234; //throw new Exception("A busca deve chegar a um estado_atual marcado");
                }
                else
                {
                    offspring.Add((tempo, newSeq.ToArray(), offspringDivState.ToArray())); // salva as novas sequencias (filhos encontrados)
                }
            }
            return offspring; // retorna as novas sequencias q foram encontradas 
        }

        


    }
}
