interface CodeBlockProps {
  code: string;
  language?: string;
}

export function CodeBlock({ code, language }: CodeBlockProps) {
  return (
    <div className="bg-muted/50 rounded-md p-4 overflow-x-auto border">
      <pre>
        <code className={`language-${language} font-code text-sm`}>
          {code}
        </code>
      </pre>
    </div>
  );
}
