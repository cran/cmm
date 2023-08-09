\name{cmm-package}
\alias{cmm-package}
\alias{cmm}
\docType{package}

\title{
Categorical Marginal Models
}
\description{
Quite extensive package for maximum likelihood estimation and weighted least squares estimation of categorical marginal models (CMMs; e.g., Bergsma & Rudas, 2002; Bergsma, Croon and Hagenaars, 2009}
\details{
\tabular{ll}{
Package: \tab cmm\cr
Type: \tab Package\cr
Version: \tab 1.0 \cr
Date: \tab 2023-08-08\cr
License: \tab GPL (>= 2)\cr
}
The package contains principal functions for analyzing marginal models for categorical data.
All functions are illustrated using examples from the book Marginal Models for Dependent,
Clustered, and Longitudunal Categorical Data (Bergsma, Croon, & Hagenaars, 2009).

The package contains the following functions
 \code{\link{ConstraintMatrix}}
 \code{\link{DesignMatrix}}
 \code{\link{DirectSum}}
 \code{\link{JoinModels}}
 \code{\link{MarginalMatrix}}
 \code{\link{MarginalModelFit}}
 \code{\link{ModelStatistics}}
 \code{\link{SampleStatistics}}
 \code{\link{SpecifyCoefficient}}

The package contains the following data sets
 \code{\link{Antisemitism}}
 \code{\link{BodySatisfaction}}
 \code{\link{ClarenceThomas}}
 \code{\link{DutchConcern}}
 \code{\link{DutchPolitics}}
 \code{\link{ErieCounty}}
 \code{\link{EVS}}
 \code{\link{GSS93}}
 \code{\link{LaborParticipation}}
 \code{\link{MarihuanaAlcohol}}
 \code{\link{NES}}
 \code{\link{NKPS}}
 \code{\link{NKPS2}}
 \code{\link{Smoking}}
 
As of version 1.0, the option of maximum augmented empirical likelihood estimation (MAEL) estimation (Van der Ark et al., 2023), which is particularly useful for large data set.
The following functions were added: 
 \code{\link{Margins}}
 \code{\link{RecordsToFrequencies}};
the following data set was added \code{\link{acl}};
and the following function was updated: \code{\link{MarginalMatrix}}.

}
\author{
Wicher P. Bergsma
Maintainer: L. Andries van der Ark \email{L.A.vanderArk@uva.nl}.
}

\references{
  Bergsma, W. P. (1997).
  \emph{Marginal models for categorical data}.
  Tilburg, The Netherlands: Tilburg University Press.
  \url{http://stats.lse.ac.uk/bergsma/pdf/bergsma_phdthesis.pdf}

  Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
  Marginal models for dependent, clustered, and longitudunal categorical data.
  Berlin: Springer. \doi{10.1007/b12532}

  Bergsma, W. P.& Rudas T. (2002). Marginal models for categorical data.
  \emph{The Annals of Statistics, 30}, 1, 140-159. 
  \doi{10.1214/aos/1015362188}
  
  Van der Ark, L. A., Bergsma, W. P., & Koopman L. (2023)
  Maximum augmented empirical likelihood estimation of categorical marginal models for large sparse contingency tables. 
  Paper submitted for publication.

}

\keyword{package}
