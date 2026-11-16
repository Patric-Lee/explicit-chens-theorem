import PlattAssemblyKernel
import PlattCertificates.Count131072.C066208
import PlattCertificates.Count131072.C066209
import PlattCertificates.Count131072.C066210
import PlattCertificates.Count131072.C066211
import PlattCertificates.Count131072.C066212
import PlattCertificates.Count131072.C066213
import PlattCertificates.Count131072.C066214
import PlattCertificates.Count131072.C066215
import PlattCertificates.Count131072.C066216
import PlattCertificates.Count131072.C066217
import PlattCertificates.Count131072.C066218
import PlattCertificates.Count131072.C066219
import PlattCertificates.Count131072.C066220
import PlattCertificates.Count131072.C066221
import PlattCertificates.Count131072.C066222
import PlattCertificates.Count131072.C066223
import PlattCertificates.Count131072.C066224
import PlattCertificates.Count131072.C066225
import PlattCertificates.Count131072.C066226
import PlattCertificates.Count131072.C066227
import PlattCertificates.Count131072.C066228
import PlattCertificates.Count131072.C066229
import PlattCertificates.Count131072.C066230
import PlattCertificates.Count131072.C066231
import PlattCertificates.Count131072.C066232
import PlattCertificates.Count131072.C066233
import PlattCertificates.Count131072.C066234
import PlattCertificates.Count131072.C066235
import PlattCertificates.Count131072.C066236
import PlattCertificates.Count131072.C066237
import PlattCertificates.Count131072.C066238
import PlattCertificates.Count131072.C066239
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000194
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66208 : List PrefixCut := [⟨64,187001250,187001358⟩]
theorem checked66208 : checkPrefixCuts (2^48) 8681947137 10 Manual.Count131072.C066208.packed 64 cuts66208 = true := by
 decide +kernel
def cuts66209 : List PrefixCut := [⟨58,168227384,168227481⟩,
⟨64,184955977,184956084⟩]
theorem checked66209 : checkPrefixCuts (2^48) 8682078209 10 Manual.Count131072.C066209.packed 64 cuts66209 = true := by
 decide +kernel
def pointBounds66209 : List (Nat × Nat × Nat) := [(8682196992,115130223894415,115130612999957)]
theorem point_links_checked66209 : (cuts66209.take 1).map (fun c => (8682078209-1+2*2^10*c.k,115130055667031+c.lower,115130444772476+c.upper)) = pointBounds66209 := by
 decide +kernel
def cuts66210 : List PrefixCut := [⟨64,184758655,184758767⟩]
theorem checked66210 : checkPrefixCuts (2^48) 8682209281 10 Manual.Count131072.C066210.packed 64 cuts66210 = true := by
 decide +kernel
def cuts66211 : List PrefixCut := [⟨63,182486552,182486658⟩,
⟨64,185566334,185566442⟩]
theorem checked66211 : checkPrefixCuts (2^48) 8682340353 10 Manual.Count131072.C066211.packed 64 cuts66211 = true := by
 decide +kernel
def pointBounds66211 : List (Nat × Nat × Nat) := [(8682469376,115130607868215,115130996973985)]
theorem point_links_checked66211 : (cuts66211.take 1).map (fun c => (8682340353-1+2*2^10*c.k,115130425381663+c.lower,115130814487327+c.upper)) = pointBounds66211 := by
 decide +kernel
def cuts66212 : List PrefixCut := [⟨64,184558567,184558671⟩]
theorem checked66212 : checkPrefixCuts (2^48) 8682471425 10 Manual.Count131072.C066212.packed 64 cuts66212 = true := by
 decide +kernel
def cuts66213 : List PrefixCut := [⟨64,184653042,184653141⟩]
theorem checked66213 : checkPrefixCuts (2^48) 8682602497 10 Manual.Count131072.C066213.packed 64 cuts66213 = true := by
 decide +kernel
def cuts66214 : List PrefixCut := [⟨4,12156659,12156667⟩,
⟨64,184455758,184455872⟩]
theorem checked66214 : checkPrefixCuts (2^48) 8682733569 10 Manual.Count131072.C066214.packed 64 cuts66214 = true := by
 decide +kernel
def pointBounds66214 : List (Nat × Nat × Nat) := [(8682741760,115130992316265,115131381422248)]
theorem point_links_checked66214 : (cuts66214.take 1).map (fun c => (8682733569-1+2*2^10*c.k,115130980159606+c.lower,115131369265581+c.upper)) = pointBounds66214 := by
 decide +kernel
def cuts66215 : List PrefixCut := [⟨64,188180922,188181029⟩]
theorem checked66215 : checkPrefixCuts (2^48) 8682864641 10 Manual.Count131072.C066215.packed 64 cuts66215 = true := by
 decide +kernel
def cuts66216 : List PrefixCut := [⟨9,26484494,26484511⟩,
⟨64,184450168,184450273⟩]
theorem checked66216 : checkPrefixCuts (2^48) 8682995713 10 Manual.Count131072.C066216.packed 64 cuts66216 = true := by
 decide +kernel
def pointBounds66216 : List (Nat × Nat × Nat) := [(8683014144,115131379280780,115131768386993)]
theorem point_links_checked66216 : (cuts66216.take 1).map (fun c => (8682995713-1+2*2^10*c.k,115131352796286+c.lower,115131741902482+c.upper)) = pointBounds66216 := by
 decide +kernel
def cuts66217 : List PrefixCut := [⟨64,184058388,184058498⟩]
theorem checked66217 : checkPrefixCuts (2^48) 8683126785 10 Manual.Count131072.C066217.packed 64 cuts66217 = true := by
 decide +kernel
def cuts66218 : List PrefixCut := [⟨14,38477512,38477531⟩,
⟨64,186324689,186324790⟩]
theorem checked66218 : checkPrefixCuts (2^48) 8683257857 10 Manual.Count131072.C066218.packed 64 cuts66218 = true := by
 decide +kernel
def pointBounds66218 : List (Nat × Nat × Nat) := [(8683286528,115131759782354,115132148888784)]
theorem point_links_checked66218 : (cuts66218.take 1).map (fun c => (8683257857-1+2*2^10*c.k,115131721304842+c.lower,115132110411253+c.upper)) = pointBounds66218 := by
 decide +kernel
def cuts66219 : List PrefixCut := [⟨64,184668718,184668828⟩]
theorem checked66219 : checkPrefixCuts (2^48) 8683388929 10 Manual.Count131072.C066219.packed 64 cuts66219 = true := by
 decide +kernel
def cuts66220 : List PrefixCut := [⟨19,55267174,55267209⟩,
⟨64,185670794,185670903⟩]
theorem checked66220 : checkPrefixCuts (2^48) 8683520001 10 Manual.Count131072.C066220.packed 64 cuts66220 = true := by
 decide +kernel
def pointBounds66220 : List (Nat × Nat × Nat) := [(8683558912,115132147565423,115132536672080)]
theorem point_links_checked66220 : (cuts66220.take 1).map (fun c => (8683520001-1+2*2^10*c.k,115132092298249+c.lower,115132481404871+c.upper)) = pointBounds66220 := by
 decide +kernel
def cuts66221 : List PrefixCut := [⟨64,187288692,187288796⟩]
theorem checked66221 : checkPrefixCuts (2^48) 8683651073 10 Manual.Count131072.C066221.packed 64 cuts66221 = true := by
 decide +kernel
def cuts66222 : List PrefixCut := [⟨24,68004086,68004126⟩,
⟨64,182164523,182164626⟩]
theorem checked66222 : checkPrefixCuts (2^48) 8683782145 10 Manual.Count131072.C066222.packed 64 cuts66222 = true := by
 decide +kernel
def pointBounds66222 : List (Nat × Nat × Nat) := [(8683831296,115132533261821,115132922368696)]
theorem point_links_checked66222 : (cuts66222.take 1).map (fun c => (8683782145-1+2*2^10*c.k,115132465257735+c.lower,115132854364570+c.upper)) = pointBounds66222 := by
 decide +kernel
def cuts66223 : List PrefixCut := [⟨64,187412687,187412791⟩]
theorem checked66223 : checkPrefixCuts (2^48) 8683913217 10 Manual.Count131072.C066223.packed 64 cuts66223 = true := by
 decide +kernel
def cuts66224 : List PrefixCut := [⟨29,82944281,82944323⟩,
⟨64,183228634,183228732⟩]
theorem checked66224 : checkPrefixCuts (2^48) 8684044289 10 Manual.Count131072.C066224.packed 64 cuts66224 = true := by
 decide +kernel
def pointBounds66224 : List (Nat × Nat × Nat) := [(8684103680,115132917779226,115133306886310)]
theorem point_links_checked66224 : (cuts66224.take 1).map (fun c => (8684044289-1+2*2^10*c.k,115132834834945+c.lower,115133223941987+c.upper)) = pointBounds66224 := by
 decide +kernel
def cuts66225 : List PrefixCut := [⟨64,185073357,185073461⟩]
theorem checked66225 : checkPrefixCuts (2^48) 8684175361 10 Manual.Count131072.C066225.packed 64 cuts66225 = true := by
 decide +kernel
def cuts66226 : List PrefixCut := [⟨34,99212442,99212498⟩,
⟨64,184746466,184746565⟩]
theorem checked66226 : checkPrefixCuts (2^48) 8684306433 10 Manual.Count131072.C066226.packed 64 cuts66226 = true := by
 decide +kernel
def pointBounds66226 : List (Nat × Nat × Nat) := [(8684376064,115133302349378,115133691456678)]
theorem point_links_checked66226 : (cuts66226.take 1).map (fun c => (8684306433-1+2*2^10*c.k,115133203136936+c.lower,115133592244180+c.upper)) = pointBounds66226 := by
 decide +kernel
def cuts66227 : List PrefixCut := [⟨64,184451967,184452079⟩]
theorem checked66227 : checkPrefixCuts (2^48) 8684437505 10 Manual.Count131072.C066227.packed 64 cuts66227 = true := by
 decide +kernel
def cuts66228 : List PrefixCut := [⟨39,112173695,112173757⟩,
⟨64,184092662,184092766⟩]
theorem checked66228 : checkPrefixCuts (2^48) 8684568577 10 Manual.Count131072.C066228.packed 64 cuts66228 = true := by
 decide +kernel
def pointBounds66228 : List (Nat × Nat × Nat) := [(8684648448,115133684509064,115134073616581)]
theorem point_links_checked66228 : (cuts66228.take 1).map (fun c => (8684568577-1+2*2^10*c.k,115133572335369+c.lower,115133961442824+c.upper)) = pointBounds66228 := by
 decide +kernel
def cuts66229 : List PrefixCut := [⟨64,187136437,187136549⟩]
theorem checked66229 : checkPrefixCuts (2^48) 8684699649 10 Manual.Count131072.C066229.packed 64 cuts66229 = true := by
 decide +kernel
def cuts66230 : List PrefixCut := [⟨44,127791753,127791827⟩,
⟨64,186323371,186323480⟩]
theorem checked66230 : checkPrefixCuts (2^48) 8684830721 10 Manual.Count131072.C066230.packed 64 cuts66230 = true := by
 decide +kernel
def pointBounds66230 : List (Nat × Nat × Nat) := [(8684920832,115134071356221,115134460463966)]
theorem point_links_checked66230 : (cuts66230.take 1).map (fun c => (8684830721-1+2*2^10*c.k,115133943564468+c.lower,115134332672139+c.upper)) = pointBounds66230 := by
 decide +kernel
def cuts66231 : List PrefixCut := [⟨64,186871523,186871629⟩]
theorem checked66231 : checkPrefixCuts (2^48) 8684961793 10 Manual.Count131072.C066231.packed 64 cuts66231 = true := by
 decide +kernel
def cuts66232 : List PrefixCut := [⟨49,141399502,141399582⟩,
⟨64,184859349,184859454⟩]
theorem checked66232 : checkPrefixCuts (2^48) 8685092865 10 Manual.Count131072.C066232.packed 64 cuts66232 = true := by
 decide +kernel
def pointBounds66232 : List (Nat × Nat × Nat) := [(8685193216,115134458158864,115134847266830)]
theorem point_links_checked66232 : (cuts66232.take 1).map (fun c => (8685092865-1+2*2^10*c.k,115134316759362+c.lower,115134705867248+c.upper)) = pointBounds66232 := by
 decide +kernel
def cuts66233 : List PrefixCut := [⟨64,184208411,184208518⟩]
theorem checked66233 : checkPrefixCuts (2^48) 8685223937 10 Manual.Count131072.C066233.packed 64 cuts66233 = true := by
 decide +kernel
def cuts66234 : List PrefixCut := [⟨54,156529582,156529679⟩,
⟨64,185015809,185015924⟩]
theorem checked66234 : checkPrefixCuts (2^48) 8685355009 10 Manual.Count131072.C066234.packed 64 cuts66234 = true := by
 decide +kernel
def pointBounds66234 : List (Nat × Nat × Nat) := [(8685465600,115134842356704,115135231464899)]
theorem point_links_checked66234 : (cuts66234.take 1).map (fun c => (8685355009-1+2*2^10*c.k,115134685827122+c.lower,115135074935220+c.upper)) = pointBounds66234 := by
 decide +kernel
def cuts66235 : List PrefixCut := [⟨64,185369501,185369606⟩]
theorem checked66235 : checkPrefixCuts (2^48) 8685486081 10 Manual.Count131072.C066235.packed 64 cuts66235 = true := by
 decide +kernel
def cuts66236 : List PrefixCut := [⟨59,171334676,171334775⟩,
⟨64,185820401,185820507⟩]
theorem checked66236 : checkPrefixCuts (2^48) 8685617153 10 Manual.Count131072.C066236.packed 64 cuts66236 = true := by
 decide +kernel
def pointBounds66236 : List (Nat × Nat × Nat) := [(8685737984,115135227547108,115135616655525)]
theorem point_links_checked66236 : (cuts66236.take 1).map (fun c => (8685617153-1+2*2^10*c.k,115135056212432+c.lower,115135445320750+c.upper)) = pointBounds66236 := by
 decide +kernel
def cuts66237 : List PrefixCut := [⟨64,186368510,186368616⟩]
theorem checked66237 : checkPrefixCuts (2^48) 8685748225 10 Manual.Count131072.C066237.packed 64 cuts66237 = true := by
 decide +kernel
def cuts66238 : List PrefixCut := [⟨64,186074057,186074166⟩]
theorem checked66238 : checkPrefixCuts (2^48) 8685879297 10 Manual.Count131072.C066238.packed 64 cuts66238 = true := by
 decide +kernel
def pointBounds66238 : List (Nat × Nat × Nat) := [(8686010368,115135614475400,115136003584039)]
theorem point_links_checked66238 : (cuts66238.take 1).map (fun c => (8685879297-1+2*2^10*c.k,115135428401343+c.lower,115135817509873+c.upper)) = pointBounds66238 := by
 decide +kernel
def cuts66239 : List PrefixCut := [⟨64,185779584,185779695⟩]
theorem checked66239 : checkPrefixCuts (2^48) 8686010369 10 Manual.Count131072.C066239.packed 64 cuts66239 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000194
