'use client';

import { useEffect, useState } from 'react';
import type { CounterexampleStep } from '@/lib/mock-data';
import { cn } from '@/lib/utils';
import { Server, ShieldAlert } from 'lucide-react';

interface ProtocolVisualizationProps {
  traceStep: CounterexampleStep;
}

const NUM_NODES = 4;

export default function ProtocolVisualization({ traceStep }: ProtocolVisualizationProps) {
  const [nodes, setNodes] = useState<any[]>([]);
  const [messages, setMessages] = useState<any[]>([]);

  useEffect(() => {
    const nodeStates = traceStep.state.nodes || Array(NUM_NODES).fill({ status: 'idle', id: 0 }).map((n, i) => ({ ...n, id: i }));
    setNodes(nodeStates);
    const messageStates = traceStep.state.messages || [];
    setMessages(messageStates);
  }, [traceStep]);

  const radius = 120;
  const center = 150;

  const getNodePos = (index: number) => {
    const angle = (index / NUM_NODES) * 2 * Math.PI - Math.PI / 2;
    return {
      x: center + radius * Math.cos(angle),
      y: center + radius * Math.sin(angle),
    };
  };

  return (
    <div className="w-full aspect-square relative flex items-center justify-center bg-muted/30 rounded-lg p-4 overflow-hidden">
      <div className="relative w-[300px] h-[300px]">
        {nodes.map((node, i) => {
          const { x, y } = getNodePos(i);
          const colorClass = 
            node.status === 'byzantine' ? 'text-destructive' :
            node.status === 'proposing' ? 'text-accent' :
            node.status === 'voted' ? 'text-primary' :
            'text-foreground/80';
          
          return (
            <div
              key={`node-${i}-${traceStep.step}`}
              className="absolute transition-all duration-500 animate-in fade-in zoom-in-50"
              style={{ left: x - 20, top: y - 20, width: 40, height: 40 }}
            >
              <div className="relative w-full h-full flex items-center justify-center flex-col">
                {node.status === 'byzantine' ? <ShieldAlert className={cn("w-8 h-8", colorClass)} /> : <Server className={cn("w-8 h-8", colorClass)} /> }
                <span className="absolute -bottom-5 text-xs font-semibold">Node {i}</span>
              </div>
            </div>
          );
        })}
        
        <svg className="absolute top-0 left-0 w-full h-full overflow-visible">
          <defs>
            <marker id="arrowhead" markerWidth="10" markerHeight="7" refX="8" refY="3.5" orient="auto">
              <polygon points="0 0, 10 3.5, 0 7" className="fill-accent/50" />
            </marker>
          </defs>
          {messages.map((msg, i) => {
            const fromPos = getNodePos(msg.from);
            const toPos = getNodePos(msg.to);
            return (
              <g key={`msg-${i}-${traceStep.step}`} className="animate-in fade-in duration-1000">
                <line 
                  x1={fromPos.x} y1={fromPos.y}
                  x2={toPos.x} y2={toPos.y}
                  className="stroke-accent/50"
                  strokeWidth="2"
                  markerEnd="url(#arrowhead)"
                />
                <circle cx={fromPos.x + (toPos.x - fromPos.x) / 2} cy={fromPos.y + (toPos.y-fromPos.y)/2} r="10" className="fill-accent">
                   <title>{msg.type}</title>
                </circle>
              </g>
            );
          })}
        </svg>

      </div>
    </div>
  );
}
