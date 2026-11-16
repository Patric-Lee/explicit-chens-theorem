import PlattAssemblyKernel
import PlattCertificates.Count131072.C051216
import PlattCertificates.Count131072.C051217
import PlattCertificates.Count131072.C051218
import PlattCertificates.Count131072.C051219
import PlattCertificates.Count131072.C051220
import PlattCertificates.Count131072.C051221
import PlattCertificates.Count131072.C051222
import PlattCertificates.Count131072.C051223
import PlattCertificates.Count131072.C051224
import PlattCertificates.Count131072.C051225
import PlattCertificates.Count131072.C051226
import PlattCertificates.Count131072.C051227
import PlattCertificates.Count131072.C051228
import PlattCertificates.Count131072.C051229
import PlattCertificates.Count131072.C051230
import PlattCertificates.Count131072.C051231
import PlattCertificates.Count131072.C051232
import PlattCertificates.Count131072.C051233
import PlattCertificates.Count131072.C051234
import PlattCertificates.Count131072.C051235
import PlattCertificates.Count131072.C051236
import PlattCertificates.Count131072.C051237
import PlattCertificates.Count131072.C051238
import PlattCertificates.Count131072.C051239
import PlattCertificates.Count131072.C051240
import PlattCertificates.Count131072.C051241
import PlattCertificates.Count131072.C051242
import PlattCertificates.Count131072.C051243
import PlattCertificates.Count131072.C051244
import PlattCertificates.Count131072.C051245
import PlattCertificates.Count131072.C051246
import PlattCertificates.Count131072.C051247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51216 : List PrefixCut := [⟨64,244138374,244138513⟩]
theorem checked51216 : checkPrefixCuts (2^48) 6716915713 10 Manual.Count131072.C051216.packed 64 cuts51216 = true := by
 decide +kernel
def cuts51217 : List PrefixCut := [⟨9,33984553,33984572⟩,
⟨64,240739369,240739504⟩]
theorem checked51217 : checkPrefixCuts (2^48) 6717046785 10 Manual.Count131072.C051217.packed 64 cuts51217 = true := by
 decide +kernel
def pointBounds51217 : List (Nat × Nat × Nat) := [(6717065216,111956019840831,111956407133013)]
theorem point_links_checked51217 : (cuts51217.take 1).map (fun c => (6717046785-1+2*2^10*c.k,111955985856278+c.lower,111956373148441+c.upper)) = pointBounds51217 := by
 decide +kernel
def cuts51218 : List PrefixCut := [⟨48,182238056,182238158⟩,
⟨64,243123155,243123291⟩]
theorem checked51218 : checkPrefixCuts (2^48) 6717177857 10 Manual.Count131072.C051218.packed 64 cuts51218 = true := by
 decide +kernel
def pointBounds51218 : List (Nat × Nat × Nat) := [(6717276160,111956408833703,111956796126103)]
theorem point_links_checked51218 : (cuts51218.take 1).map (fun c => (6717177857-1+2*2^10*c.k,111956226595647+c.lower,111956613887945+c.upper)) = pointBounds51218 := by
 decide +kernel
def cuts51219 : List PrefixCut := [⟨64,242908873,242909010⟩]
theorem checked51219 : checkPrefixCuts (2^48) 6717308929 10 Manual.Count131072.C051219.packed 64 cuts51219 = true := by
 decide +kernel
def cuts51220 : List PrefixCut := [⟨23,85438098,85438147⟩,
⟨64,242820335,242820467⟩]
theorem checked51220 : checkPrefixCuts (2^48) 6717440001 10 Manual.Count131072.C051220.packed 64 cuts51220 = true := by
 decide +kernel
def pointBounds51220 : List (Nat × Nat × Nat) := [(6717487104,111956798065773,111957185358393)]
theorem point_links_checked51220 : (cuts51220.take 1).map (fun c => (6717440001-1+2*2^10*c.k,111956712627675+c.lower,111957099920246+c.upper)) = pointBounds51220 := by
 decide +kernel
def cuts51221 : List PrefixCut := [⟨62,239254121,239254255⟩,
⟨64,245790596,245790734⟩]
theorem checked51221 : checkPrefixCuts (2^48) 6717571073 10 Manual.Count131072.C051221.packed 64 cuts51221 = true := by
 decide +kernel
def pointBounds51221 : List (Nat × Nat × Nat) := [(6717698048,111957194702131,111957581994968)]
theorem point_links_checked51221 : (cuts51221.take 1).map (fun c => (6717571073-1+2*2^10*c.k,111956955448010+c.lower,111957342740713+c.upper)) = pointBounds51221 := by
 decide +kernel
def cuts51222 : List PrefixCut := [⟨64,242014773,242014911⟩]
theorem checked51222 : checkPrefixCuts (2^48) 6717702145 10 Manual.Count131072.C051222.packed 64 cuts51222 = true := by
 decide +kernel
def cuts51223 : List PrefixCut := [⟨37,140782052,140782132⟩,
⟨64,244565905,244566042⟩]
theorem checked51223 : checkPrefixCuts (2^48) 6717833217 10 Manual.Count131072.C051223.packed 64 cuts51223 = true := by
 decide +kernel
def pointBounds51223 : List (Nat × Nat × Nat) := [(6717908992,111957584035431,111957971328490)]
theorem point_links_checked51223 : (cuts51223.take 1).map (fun c => (6717833217-1+2*2^10*c.k,111957443253379+c.lower,111957830546358+c.upper)) = pointBounds51223 := by
 decide +kernel
def cuts51224 : List PrefixCut := [⟨64,244393534,244393676⟩]
theorem checked51224 : checkPrefixCuts (2^48) 6717964289 10 Manual.Count131072.C051224.packed 64 cuts51224 = true := by
 decide +kernel
def cuts51225 : List PrefixCut := [⟨12,45165983,45166007⟩,
⟨64,241036976,241037111⟩]
theorem checked51225 : checkPrefixCuts (2^48) 6718095361 10 Manual.Count131072.C051225.packed 64 cuts51225 = true := by
 decide +kernel
def pointBounds51225 : List (Nat × Nat × Nat) := [(6718119936,111957977378801,111958364672083)]
theorem point_links_checked51225 : (cuts51225.take 1).map (fun c => (6718095361-1+2*2^10*c.k,111957932212818+c.lower,111958319506076+c.upper)) = pointBounds51225 := by
 decide +kernel
def cuts51226 : List PrefixCut := [⟨51,194066326,194066433⟩,
⟨64,243755534,243755669⟩]
theorem checked51226 : checkPrefixCuts (2^48) 6718226433 10 Manual.Count131072.C051226.packed 64 cuts51226 = true := by
 decide +kernel
def pointBounds51226 : List (Nat × Nat × Nat) := [(6718330880,111958367316120,111958754609620)]
theorem point_links_checked51226 : (cuts51226.take 1).map (fun c => (6718226433-1+2*2^10*c.k,111958173249794+c.lower,111958560543187+c.upper)) = pointBounds51226 := by
 decide +kernel
def cuts51227 : List PrefixCut := [⟨64,241488397,241488535⟩]
theorem checked51227 : checkPrefixCuts (2^48) 6718357505 10 Manual.Count131072.C051227.packed 64 cuts51227 = true := by
 decide +kernel
def cuts51228 : List PrefixCut := [⟨26,97825763,97825817⟩,
⟨64,242279712,242279850⟩]
theorem checked51228 : checkPrefixCuts (2^48) 6718488577 10 Manual.Count131072.C051228.packed 64 cuts51228 = true := by
 decide +kernel
def pointBounds51228 : List (Nat × Nat × Nat) := [(6718541824,111958756319488,111959143613208)]
theorem point_links_checked51228 : (cuts51228.take 1).map (fun c => (6718488577-1+2*2^10*c.k,111958658493725+c.lower,111959045787391+c.upper)) = pointBounds51228 := by
 decide +kernel
def cuts51229 : List PrefixCut := [⟨64,242149290,242149427⟩]
theorem checked51229 : checkPrefixCuts (2^48) 6718619649 10 Manual.Count131072.C051229.packed 64 cuts51229 = true := by
 decide +kernel
def cuts51230 : List PrefixCut := [⟨1,4231287,4231289⟩,
⟨64,244993337,244993472⟩]
theorem checked51230 : checkPrefixCuts (2^48) 6718750721 10 Manual.Count131072.C051230.packed 64 cuts51230 = true := by
 decide +kernel
def pointBounds51230 : List (Nat × Nat × Nat) := [(6718752768,111959147154014,111959534447957)]
theorem point_links_checked51230 : (cuts51230.take 1).map (fun c => (6718750721-1+2*2^10*c.k,111959142922727+c.lower,111959530216668+c.upper)) = pointBounds51230 := by
 decide +kernel
def cuts51231 : List PrefixCut := [⟨40,150604833,150604918⟩,
⟨64,239165473,239165609⟩]
theorem checked51231 : checkPrefixCuts (2^48) 6718881793 10 Manual.Count131072.C051231.packed 64 cuts51231 = true := by
 decide +kernel
def pointBounds51231 : List (Nat × Nat × Nat) := [(6718963712,111959538520897,111959925815058)]
theorem point_links_checked51231 : (cuts51231.take 1).map (fun c => (6718881793-1+2*2^10*c.k,111959387916064+c.lower,111959775210140+c.upper)) = pointBounds51231 := by
 decide +kernel
def cuts51232 : List PrefixCut := [⟨64,239370267,239370404⟩]
theorem checked51232 : checkPrefixCuts (2^48) 6719012865 10 Manual.Count131072.C051232.packed 64 cuts51232 = true := by
 decide +kernel
def cuts51233 : List PrefixCut := [⟨15,56302025,56302057⟩,
⟨64,238862912,238863048⟩]
theorem checked51233 : checkPrefixCuts (2^48) 6719143937 10 Manual.Count131072.C051233.packed 64 cuts51233 = true := by
 decide +kernel
def pointBounds51233 : List (Nat × Nat × Nat) := [(6719174656,111959922753829,111960310048210)]
theorem point_links_checked51233 : (cuts51233.take 1).map (fun c => (6719143937-1+2*2^10*c.k,111959866451804+c.lower,111960253746153+c.upper)) = pointBounds51233 := by
 decide +kernel
def cuts51234 : List PrefixCut := [⟨54,204843674,204843793⟩,
⟨64,241162228,241162367⟩]
theorem checked51234 : checkPrefixCuts (2^48) 6719275009 10 Manual.Count131072.C051234.packed 64 cuts51234 = true := by
 decide +kernel
def pointBounds51234 : List (Nat × Nat × Nat) := [(6719385600,111960310158390,111960697452994)]
theorem point_links_checked51234 : (cuts51234.take 1).map (fun c => (6719275009-1+2*2^10*c.k,111960105314716+c.lower,111960492609201+c.upper)) = pointBounds51234 := by
 decide +kernel
def cuts51235 : List PrefixCut := [⟨64,241534499,241534634⟩]
theorem checked51235 : checkPrefixCuts (2^48) 6719406081 10 Manual.Count131072.C051235.packed 64 cuts51235 = true := by
 decide +kernel
def cuts51236 : List PrefixCut := [⟨29,107109783,107109845⟩,
⟨64,241822998,241823138⟩]
theorem checked51236 : checkPrefixCuts (2^48) 6719537153 10 Manual.Count131072.C051236.packed 64 cuts51236 = true := by
 decide +kernel
def pointBounds51236 : List (Nat × Nat × Nat) := [(6719596544,111960695121226,111961082416047)]
theorem point_links_checked51236 : (cuts51236.take 1).map (fun c => (6719537153-1+2*2^10*c.k,111960588011443+c.lower,111960975306202+c.upper)) = pointBounds51236 := by
 decide +kernel
def cuts51237 : List PrefixCut := [⟨64,247556938,247557075⟩]
theorem checked51237 : checkPrefixCuts (2^48) 6719668225 10 Manual.Count131072.C051237.packed 64 cuts51237 = true := by
 decide +kernel
def cuts51238 : List PrefixCut := [⟨4,15163229,15163237⟩,
⟨64,242902645,242902781⟩]
theorem checked51238 : checkPrefixCuts (2^48) 6719799297 10 Manual.Count131072.C051238.packed 64 cuts51238 = true := by
 decide +kernel
def pointBounds51238 : List (Nat × Nat × Nat) := [(6719807488,111961092554608,111961479849652)]
theorem point_links_checked51238 : (cuts51238.take 1).map (fun c => (6719799297-1+2*2^10*c.k,111961077391379+c.lower,111961464686415+c.upper)) = pointBounds51238 := by
 decide +kernel
def cuts51239 : List PrefixCut := [⟨43,160675873,160675963⟩,
⟨64,239547017,239547152⟩]
theorem checked51239 : checkPrefixCuts (2^48) 6719930369 10 Manual.Count131072.C051239.packed 64 cuts51239 = true := by
 decide +kernel
def pointBounds51239 : List (Nat × Nat × Nat) := [(6720018432,111961480969897,111961868265159)]
theorem point_links_checked51239 : (cuts51239.take 1).map (fun c => (6719930369-1+2*2^10*c.k,111961320294024+c.lower,111961707589196+c.upper)) = pointBounds51239 := by
 decide +kernel
def cuts51240 : List PrefixCut := [⟨64,243437689,243437827⟩]
theorem checked51240 : checkPrefixCuts (2^48) 6720061441 10 Manual.Count131072.C051240.packed 64 cuts51240 = true := by
 decide +kernel
def cuts51241 : List PrefixCut := [⟨18,68188505,68188542⟩,
⟨64,241380582,241380717⟩]
theorem checked51241 : checkPrefixCuts (2^48) 6720192513 10 Manual.Count131072.C051241.packed 64 cuts51241 = true := by
 decide +kernel
def pointBounds51241 : List (Nat × Nat × Nat) := [(6720229376,111961871467235,111962258762717)]
theorem point_links_checked51241 : (cuts51241.take 1).map (fun c => (6720192513-1+2*2^10*c.k,111961803278730+c.lower,111962190574175+c.upper)) = pointBounds51241 := by
 decide +kernel
def cuts51242 : List PrefixCut := [⟨57,219052089,219052214⟩,
⟨64,246527571,246527712⟩]
theorem checked51242 : checkPrefixCuts (2^48) 6720323585 10 Manual.Count131072.C051242.packed 64 cuts51242 = true := by
 decide +kernel
def pointBounds51242 : List (Nat × Nat × Nat) := [(6720440320,111962263711401,111962651007106)]
theorem point_links_checked51242 : (cuts51242.take 1).map (fun c => (6720323585-1+2*2^10*c.k,111962044659312+c.lower,111962431954892+c.upper)) = pointBounds51242 := by
 decide +kernel
def cuts51243 : List PrefixCut := [⟨64,243800415,243800554⟩]
theorem checked51243 : checkPrefixCuts (2^48) 6720454657 10 Manual.Count131072.C051243.packed 64 cuts51243 = true := by
 decide +kernel
def cuts51244 : List PrefixCut := [⟨32,120620995,120621063⟩,
⟨64,240989520,240989657⟩]
theorem checked51244 : checkPrefixCuts (2^48) 6720585729 10 Manual.Count131072.C051244.packed 64 cuts51244 = true := by
 decide +kernel
def pointBounds51244 : List (Nat × Nat × Nat) := [(6720651264,111962655608293,111963042904221)]
theorem point_links_checked51244 : (cuts51244.take 1).map (fun c => (6720585729-1+2*2^10*c.k,111962534987298+c.lower,111962922283158+c.upper)) = pointBounds51244 := by
 decide +kernel
def cuts51245 : List PrefixCut := [⟨64,244125936,244126076⟩]
theorem checked51245 : checkPrefixCuts (2^48) 6720716801 10 Manual.Count131072.C051245.packed 64 cuts51245 = true := by
 decide +kernel
def cuts51246 : List PrefixCut := [⟨7,26971245,26971260⟩,
⟨64,241650181,241650316⟩]
theorem checked51246 : checkPrefixCuts (2^48) 6720847873 10 Manual.Count131072.C051246.packed 64 cuts51246 = true := by
 decide +kernel
def pointBounds51246 : List (Nat × Nat × Nat) := [(6720862208,111963047073999,111963434370151)]
theorem point_links_checked51246 : (cuts51246.take 1).map (fun c => (6720847873-1+2*2^10*c.k,111963020102754+c.lower,111963407398891+c.upper)) = pointBounds51246 := by
 decide +kernel
def cuts51247 : List PrefixCut := [⟨46,173800969,173801068⟩,
⟨64,242483093,242483230⟩]
theorem checked51247 : checkPrefixCuts (2^48) 6720978945 10 Manual.Count131072.C051247.packed 64 cuts51247 = true := by
 decide +kernel
def pointBounds51247 : List (Nat × Nat × Nat) := [(6721073152,111963435553904,111963822850275)]
theorem point_links_checked51247 : (cuts51247.take 1).map (fun c => (6720978945-1+2*2^10*c.k,111963261752935+c.lower,111963649049207+c.upper)) = pointBounds51247 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000038
