import { MonacoEditorLanguageClientWrapper, UserConfig } from 'monaco-editor-wrapper';
import { configureWorker, defineUserServices } from './setupCommon.js';

export const setupConfigExtended = (): UserConfig => {
    const extensionFilesOrContents = new Map();
    extensionFilesOrContents.set('/language-configuration.json', new URL('../language-configuration.json', import.meta.url));
    extensionFilesOrContents.set('/smt-grammar.json', new URL('../syntaxes/smt.tmLanguage.json', import.meta.url));

    return {
        wrapperConfig: {
            serviceConfig: defineUserServices(),
            editorAppConfig: {
                $type: 'extended',
                languageId: 'smt',
                code: `; SMT is running in the web!`,
                useDiffEditor: false,
                extensions: [{
                    config: {
                        name: 'smt-web',
                        publisher: 'generator-langium',
                        version: '1.0.0',
                        engines: {
                            vscode: '*'
                        },
                        contributes: {
                            languages: [{
                                id: 'smt',
                                extensions: [
                                    '.smt'
                                ],
                                configuration: './language-configuration.json'
                            }],
                            grammars: [{
                                language: 'smt',
                                scopeName: 'source.smt',
                                path: './smt-grammar.json'
                            }]
                        }
                    },
                    filesOrContents: extensionFilesOrContents,
                }],                
                userConfiguration: {
                    json: JSON.stringify({
                        'workbench.colorTheme': 'Default Dark Modern',
                        'editor.semanticHighlighting.enabled': true
                    })
                }
            }
        },
        languageClientConfig: configureWorker()
    };
};

export const executeExtended = async (htmlElement: HTMLElement) => {
    const userConfig = setupConfigExtended();
    const wrapper = new MonacoEditorLanguageClientWrapper();
    await wrapper.initAndStart(userConfig, htmlElement);
};
