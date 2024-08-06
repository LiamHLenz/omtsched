//
// Created by Lukas Lenz
//

#ifndef OMTSCHED_TRANSLATOR_H
#define OMTSCHED_TRANSLATOR_H

#include "Problem.h"
#include "Model.h"
#include <string>

namespace omtsched {

    template<typename ID>
    class Translator {

    public:

        Translator<ID>(const Problem<ID> &problem) : problem{problem} {};

        virtual void solve() = 0;

        virtual Model<ID> getModel() = 0;
        //virtual std::vector<Model> getAllSolutions() = 0;

        //virtual void printProblem(std::string path) const = 0;
        //virtual void printSolution(std::string path) const = 0;
        //virtual void printAllSolutions(std::string path) const = 0;
        //virtual void printExplanation(std::string path) const = 0;

        bool isGenerateAllSolution() const;

        void setGenerateAllSolution(bool generateAllSolution);

        bool isGenerateExplanations() const;

        void setGenerateExplanations(bool generateExplanations);

        virtual bool isSAT() = 0;

    protected:
        const Problem<ID> &problem;
        bool generateAllSolution;
        bool generateExplanations;

    };


    template<typename ID>
    bool Translator<ID>::isGenerateAllSolution() const {
        return generateAllSolution;
    }

    template<typename ID>
    void Translator<ID>::setGenerateAllSolution(bool generateAllSolution) {
        Translator::generateAllSolution = generateAllSolution;
    }

    template<typename ID>
    bool Translator<ID>::isGenerateExplanations() const {
        return generateExplanations;
    }

    template<typename ID>
    void Translator<ID>::setGenerateExplanations(bool generateExplanations) {
        Translator::generateExplanations = generateExplanations;
    }

}


#endif //OMTSCHED_TRANSLATOR_H
