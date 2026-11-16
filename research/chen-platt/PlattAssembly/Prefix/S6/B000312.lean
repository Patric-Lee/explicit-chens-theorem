import PlattAssemblyKernel
import PlattCertificates.Count131072.C059984
import PlattCertificates.Count131072.C059985
import PlattCertificates.Count131072.C059986
import PlattCertificates.Count131072.C059987
import PlattCertificates.Count131072.C059988
import PlattCertificates.Count131072.C059989
import PlattCertificates.Count131072.C059990
import PlattCertificates.Count131072.C059991
import PlattCertificates.Count131072.C059992
import PlattCertificates.Count131072.C059993
import PlattCertificates.Count131072.C059994
import PlattCertificates.Count131072.C059995
import PlattCertificates.Count131072.C059996
import PlattCertificates.Count131072.C059997
import PlattCertificates.Count131072.C059998
import PlattCertificates.Count131072.C059999
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000312
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59984 : List PrefixCut := [⟨64,204426792,204426908⟩]
theorem checked59984 : checkPrefixCuts (2^48) 7866155009 10 Manual.Count131072.C059984.packed 64 cuts59984 = true := by
 decide +kernel
def cuts59985 : List PrefixCut := [⟨47,152074433,152074519⟩,
⟨64,206820776,206820891⟩]
theorem checked59985 : checkPrefixCuts (2^48) 7866286081 10 Manual.Count131072.C059985.packed 64 cuts59985 = true := by
 decide +kernel
def pointBounds59985 : List (Nat × Nat × Nat) := [(7866382336,113913866700974,113914255106507)]
theorem point_links_checked59985 : (cuts59985.take 1).map (fun c => (7866286081-1+2*2^10*c.k,113913714626541+c.lower,113914103031988+c.upper)) = pointBounds59985 := by
 decide +kernel
def cuts59986 : List PrefixCut := [⟨64,206924668,206924782⟩]
theorem checked59986 : checkPrefixCuts (2^48) 7866417153 10 Manual.Count131072.C059986.packed 64 cuts59986 = true := by
 decide +kernel
def cuts59987 : List PrefixCut := [⟨40,128382448,128382516⟩,
⟨64,205776234,205776346⟩]
theorem checked59987 : checkPrefixCuts (2^48) 7866548225 10 Manual.Count131072.C059987.packed 64 cuts59987 = true := by
 decide +kernel
def pointBounds59987 : List (Nat × Nat × Nat) := [(7866630144,113914256754433,113914645160177)]
theorem point_links_checked59987 : (cuts59987.take 1).map (fun c => (7866548225-1+2*2^10*c.k,113914128371985+c.lower,113914516777661+c.upper)) = pointBounds59987 := by
 decide +kernel
def cuts59988 : List PrefixCut := [⟨64,202874603,202874720⟩]
theorem checked59988 : checkPrefixCuts (2^48) 7866679297 10 Manual.Count131072.C059988.packed 64 cuts59988 = true := by
 decide +kernel
def cuts59989 : List PrefixCut := [⟨33,104334190,104334251⟩,
⟨64,203085896,203086014⟩]
theorem checked59989 : checkPrefixCuts (2^48) 7866810369 10 Manual.Count131072.C059989.packed 64 cuts59989 = true := by
 decide +kernel
def pointBounds59989 : List (Nat × Nat × Nat) := [(7866877952,113914641357012,113915029762978)]
theorem point_links_checked59989 : (cuts59989.take 1).map (fun c => (7866810369-1+2*2^10*c.k,113914537022822+c.lower,113914925428727+c.upper)) = pointBounds59989 := by
 decide +kernel
def cuts59990 : List PrefixCut := [⟨64,206338404,206338520⟩]
theorem checked59990 : checkPrefixCuts (2^48) 7866941441 10 Manual.Count131072.C059990.packed 64 cuts59990 = true := by
 decide +kernel
def cuts59991 : List PrefixCut := [⟨26,84402047,84402099⟩,
⟨64,206692760,206692879⟩]
theorem checked59991 : checkPrefixCuts (2^48) 7867072513 10 Manual.Count131072.C059991.packed 64 cuts59991 = true := by
 decide +kernel
def pointBounds59991 : List (Nat × Nat × Nat) := [(7867125760,113915030849169,113915419255360)]
theorem point_links_checked59991 : (cuts59991.take 1).map (fun c => (7867072513-1+2*2^10*c.k,113914946447122+c.lower,113915334853261+c.upper)) = pointBounds59991 := by
 decide +kernel
def cuts59992 : List PrefixCut := [⟨64,205472882,205472998⟩]
theorem checked59992 : checkPrefixCuts (2^48) 7867203585 10 Manual.Count131072.C059992.packed 64 cuts59992 = true := by
 decide +kernel
def cuts59993 : List PrefixCut := [⟨19,62217217,62217251⟩,
⟨64,206220780,206220893⟩]
theorem checked59993 : checkPrefixCuts (2^48) 7867334657 10 Manual.Count131072.C059993.packed 64 cuts59993 = true := by
 decide +kernel
def pointBounds59993 : List (Nat × Nat × Nat) := [(7867373568,113915420829981,113915809236389)]
theorem point_links_checked59993 : (cuts59993.take 1).map (fun c => (7867334657-1+2*2^10*c.k,113915358612764+c.lower,113915747019138+c.upper)) = pointBounds59993 := by
 decide +kernel
def cuts59994 : List PrefixCut := [⟨64,206038454,206038569⟩]
theorem checked59994 : checkPrefixCuts (2^48) 7867465729 10 Manual.Count131072.C059994.packed 64 cuts59994 = true := by
 decide +kernel
def cuts59995 : List PrefixCut := [⟨12,39461392,39461415⟩,
⟨64,208646675,208646791⟩]
theorem checked59995 : checkPrefixCuts (2^48) 7867596801 10 Manual.Count131072.C059995.packed 64 cuts59995 = true := by
 decide +kernel
def pointBounds59995 : List (Nat × Nat × Nat) := [(7867621376,113915810333390,113916198740015)]
theorem point_links_checked59995 : (cuts59995.take 1).map (fun c => (7867596801-1+2*2^10*c.k,113915770871998+c.lower,113916159278600+c.upper)) = pointBounds59995 := by
 decide +kernel
def cuts59996 : List PrefixCut := [⟨64,206818643,206818763⟩]
theorem checked59996 : checkPrefixCuts (2^48) 7867727873 10 Manual.Count131072.C059996.packed 64 cuts59996 = true := by
 decide +kernel
def cuts59997 : List PrefixCut := [⟨5,16349295,16349305⟩,
⟨64,206314359,206314479⟩]
theorem checked59997 : checkPrefixCuts (2^48) 7867858945 10 Manual.Count131072.C059997.packed 64 cuts59997 = true := by
 decide +kernel
def pointBounds59997 : List (Nat × Nat × Nat) := [(7867869184,113916202686611,113916591093459)]
theorem point_links_checked59997 : (cuts59997.take 1).map (fun c => (7867858945-1+2*2^10*c.k,113916186337316+c.lower,113916574744154+c.upper)) = pointBounds59997 := by
 decide +kernel
def cuts59998 : List PrefixCut := [⟨62,200837492,200837607⟩,
⟨64,207205283,207205400⟩]
theorem checked59998 : checkPrefixCuts (2^48) 7867990017 10 Manual.Count131072.C059998.packed 64 cuts59998 = true := by
 decide +kernel
def pointBounds59998 : List (Nat × Nat × Nat) := [(7868116992,113916593489167,113916981896240)]
theorem point_links_checked59998 : (cuts59998.take 1).map (fun c => (7867990017-1+2*2^10*c.k,113916392651675+c.lower,113916781058633+c.upper)) = pointBounds59998 := by
 decide +kernel
def cuts59999 : List PrefixCut := [⟨64,205341592,205341711⟩]
theorem checked59999 : checkPrefixCuts (2^48) 7868121089 10 Manual.Count131072.C059999.packed 64 cuts59999 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000312
