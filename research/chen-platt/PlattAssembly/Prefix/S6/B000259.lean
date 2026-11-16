import PlattAssemblyKernel
import PlattCertificates.Count131072.C058288
import PlattCertificates.Count131072.C058289
import PlattCertificates.Count131072.C058290
import PlattCertificates.Count131072.C058291
import PlattCertificates.Count131072.C058292
import PlattCertificates.Count131072.C058293
import PlattCertificates.Count131072.C058294
import PlattCertificates.Count131072.C058295
import PlattCertificates.Count131072.C058296
import PlattCertificates.Count131072.C058297
import PlattCertificates.Count131072.C058298
import PlattCertificates.Count131072.C058299
import PlattCertificates.Count131072.C058300
import PlattCertificates.Count131072.C058301
import PlattCertificates.Count131072.C058302
import PlattCertificates.Count131072.C058303
import PlattCertificates.Count131072.C058304
import PlattCertificates.Count131072.C058305
import PlattCertificates.Count131072.C058306
import PlattCertificates.Count131072.C058307
import PlattCertificates.Count131072.C058308
import PlattCertificates.Count131072.C058309
import PlattCertificates.Count131072.C058310
import PlattCertificates.Count131072.C058311
import PlattCertificates.Count131072.C058312
import PlattCertificates.Count131072.C058313
import PlattCertificates.Count131072.C058314
import PlattCertificates.Count131072.C058315
import PlattCertificates.Count131072.C058316
import PlattCertificates.Count131072.C058317
import PlattCertificates.Count131072.C058318
import PlattCertificates.Count131072.C058319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000259
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58288 : List PrefixCut := [⟨64,211513373,211513493⟩]
theorem checked58288 : checkPrefixCuts (2^48) 7643856897 10 Manual.Count131072.C058288.packed 64 cuts58288 = true := by
 decide +kernel
def cuts58289 : List PrefixCut := [⟨14,46654709,46654736⟩,
⟨64,213129954,213130077⟩]
theorem checked58289 : checkPrefixCuts (2^48) 7643987969 10 Manual.Count131072.C058289.packed 64 cuts58289 = true := by
 decide +kernel
def pointBounds58289 : List (Nat × Nat × Nat) := [(7644016640,113559408515775,113559796719061)]
theorem point_links_checked58289 : (cuts58289.take 1).map (fun c => (7643987969-1+2*2^10*c.k,113559361861066+c.lower,113559750064325+c.upper)) = pointBounds58289 := by
 decide +kernel
def cuts58290 : List PrefixCut := [⟨64,215188330,215188446⟩]
theorem checked58290 : checkPrefixCuts (2^48) 7644119041 10 Manual.Count131072.C058290.packed 64 cuts58290 = true := by
 decide +kernel
def cuts58291 : List PrefixCut := [⟨3,10162807,10162813⟩,
⟨64,209661423,209661542⟩]
theorem checked58291 : checkPrefixCuts (2^48) 7644250113 10 Manual.Count131072.C058291.packed 64 cuts58291 = true := by
 decide +kernel
def pointBounds58291 : List (Nat × Nat × Nat) := [(7644256256,113559800342157,113560188545661)]
theorem point_links_checked58291 : (cuts58291.take 1).map (fun c => (7644250113-1+2*2^10*c.k,113559790179350+c.lower,113560178382848+c.upper)) = pointBounds58291 := by
 decide +kernel
def cuts58292 : List PrefixCut := [⟨56,185650829,185650938⟩,
⟨64,211903886,211904011⟩]
theorem checked58292 : checkPrefixCuts (2^48) 7644381185 10 Manual.Count131072.C058292.packed 64 cuts58292 = true := by
 decide +kernel
def pointBounds58292 : List (Nat × Nat × Nat) := [(7644495872,113560185491602,113560573695328)]
theorem point_links_checked58292 : (cuts58292.take 1).map (fun c => (7644381185-1+2*2^10*c.k,113559999840773+c.lower,113560388044390+c.upper)) = pointBounds58292 := by
 decide +kernel
def cuts58293 : List PrefixCut := [⟨64,212415744,212415867⟩]
theorem checked58293 : checkPrefixCuts (2^48) 7644512257 10 Manual.Count131072.C058293.packed 64 cuts58293 = true := by
 decide +kernel
def cuts58294 : List PrefixCut := [⟨45,147205019,147205103⟩,
⟨64,209392896,209393018⟩]
theorem checked58294 : checkPrefixCuts (2^48) 7644643329 10 Manual.Count131072.C058294.packed 64 cuts58294 = true := by
 decide +kernel
def pointBounds58294 : List (Nat × Nat × Nat) := [(7644735488,113560571365422,113560959569371)]
theorem point_links_checked58294 : (cuts58294.take 1).map (fun c => (7644643329-1+2*2^10*c.k,113560424160403+c.lower,113560812364268+c.upper)) = pointBounds58294 := by
 decide +kernel
def cuts58295 : List PrefixCut := [⟨64,212518910,212519032⟩]
theorem checked58295 : checkPrefixCuts (2^48) 7644774401 10 Manual.Count131072.C058295.packed 64 cuts58295 = true := by
 decide +kernel
def cuts58296 : List PrefixCut := [⟨34,111817649,111817715⟩,
⟨64,212993895,212994022⟩]
theorem checked58296 : checkPrefixCuts (2^48) 7644905473 10 Manual.Count131072.C058296.packed 64 cuts58296 = true := by
 decide +kernel
def pointBounds58296 : List (Nat × Nat × Nat) := [(7644975104,113560957889858,113561346094033)]
theorem point_links_checked58296 : (cuts58296.take 1).map (fun c => (7644905473-1+2*2^10*c.k,113560846072209+c.lower,113561234276318+c.upper)) = pointBounds58296 := by
 decide +kernel
def cuts58297 : List PrefixCut := [⟨64,212548442,212548566⟩]
theorem checked58297 : checkPrefixCuts (2^48) 7645036545 10 Manual.Count131072.C058297.packed 64 cuts58297 = true := by
 decide +kernel
def cuts58298 : List PrefixCut := [⟨23,75953985,75954030⟩,
⟨64,212949786,212949912⟩]
theorem checked58298 : checkPrefixCuts (2^48) 7645167617 10 Manual.Count131072.C058298.packed 64 cuts58298 = true := by
 decide +kernel
def pointBounds58298 : List (Nat × Nat × Nat) := [(7645214720,113561347568531,113561735772936)]
theorem point_links_checked58298 : (cuts58298.take 1).map (fun c => (7645167617-1+2*2^10*c.k,113561271614546+c.lower,113561659818906+c.upper)) = pointBounds58298 := by
 decide +kernel
def cuts58299 : List PrefixCut := [⟨64,209853585,209853705⟩]
theorem checked58299 : checkPrefixCuts (2^48) 7645298689 10 Manual.Count131072.C058299.packed 64 cuts58299 = true := by
 decide +kernel
def cuts58300 : List PrefixCut := [⟨12,39945402,39945425⟩,
⟨64,210475850,210475971⟩]
theorem checked58300 : checkPrefixCuts (2^48) 7645429761 10 Manual.Count131072.C058300.packed 64 cuts58300 = true := by
 decide +kernel
def pointBounds58300 : List (Nat × Nat × Nat) := [(7645454336,113561734363319,113562122567948)]
theorem point_links_checked58300 : (cuts58300.take 1).map (fun c => (7645429761-1+2*2^10*c.k,113561694417917+c.lower,113562082622523+c.upper)) = pointBounds58300 := by
 decide +kernel
def cuts58301 : List PrefixCut := [⟨64,211687138,211687261⟩]
theorem checked58301 : checkPrefixCuts (2^48) 7645560833 10 Manual.Count131072.C058301.packed 64 cuts58301 = true := by
 decide +kernel
def cuts58302 : List PrefixCut := [⟨1,2982001,2982003⟩,
⟨64,214739098,214739218⟩]
theorem checked58302 : checkPrefixCuts (2^48) 7645691905 10 Manual.Count131072.C058302.packed 64 cuts58302 = true := by
 decide +kernel
def pointBounds58302 : List (Nat × Nat × Nat) := [(7645693952,113562119562906,113562507767758)]
theorem point_links_checked58302 : (cuts58302.take 1).map (fun c => (7645691905-1+2*2^10*c.k,113562116580905+c.lower,113562504785755+c.upper)) = pointBounds58302 := by
 decide +kernel
def cuts58303 : List PrefixCut := [⟨54,177811321,177811423⟩,
⟨64,211238091,211238213⟩]
theorem checked58303 : checkPrefixCuts (2^48) 7645822977 10 Manual.Count131072.C058303.packed 64 cuts58303 = true := by
 decide +kernel
def pointBounds58303 : List (Nat × Nat × Nat) := [(7645933568,113562509131324,113562897336396)]
theorem point_links_checked58303 : (cuts58303.take 1).map (fun c => (7645822977-1+2*2^10*c.k,113562331320003+c.lower,113562719524973+c.upper)) = pointBounds58303 := by
 decide +kernel
def cuts58304 : List PrefixCut := [⟨64,211823492,211823613⟩]
theorem checked58304 : checkPrefixCuts (2^48) 7645954049 10 Manual.Count131072.C058304.packed 64 cuts58304 = true := by
 decide +kernel
def cuts58305 : List PrefixCut := [⟨43,141434515,141434596⟩,
⟨64,210273732,210273854⟩]
theorem checked58305 : checkPrefixCuts (2^48) 7646085121 10 Manual.Count131072.C058305.packed 64 cuts58305 = true := by
 decide +kernel
def pointBounds58305 : List (Nat × Nat × Nat) := [(7646173184,113562895816101,113563284021395)]
theorem point_links_checked58305 : (cuts58305.take 1).map (fun c => (7646085121-1+2*2^10*c.k,113562754381586+c.lower,113563142586799+c.upper)) = pointBounds58305 := by
 decide +kernel
def cuts58306 : List PrefixCut := [⟨64,208171847,208171966⟩]
theorem checked58306 : checkPrefixCuts (2^48) 7646216193 10 Manual.Count131072.C058306.packed 64 cuts58306 = true := by
 decide +kernel
def cuts58307 : List PrefixCut := [⟨32,106090815,106090874⟩,
⟨64,210450586,210450705⟩]
theorem checked58307 : checkPrefixCuts (2^48) 7646347265 10 Manual.Count131072.C058307.packed 64 cuts58307 = true := by
 decide +kernel
def pointBounds58307 : List (Nat × Nat × Nat) := [(7646412800,113563278917980,113563667123493)]
theorem point_links_checked58307 : (cuts58307.take 1).map (fun c => (7646347265-1+2*2^10*c.k,113563172827165+c.lower,113563561032619+c.upper)) = pointBounds58307 := by
 decide +kernel
def cuts58308 : List PrefixCut := [⟨64,214532968,214533092⟩]
theorem checked58308 : checkPrefixCuts (2^48) 7646478337 10 Manual.Count131072.C058308.packed 64 cuts58308 = true := by
 decide +kernel
def cuts58309 : List PrefixCut := [⟨21,69755546,69755587⟩,
⟨64,210848273,210848393⟩]
theorem checked58309 : checkPrefixCuts (2^48) 7646609409 10 Manual.Count131072.C058309.packed 64 cuts58309 = true := by
 decide +kernel
def pointBounds58309 : List (Nat × Nat × Nat) := [(7646652416,113563667566265,113564055772003)]
theorem point_links_checked58309 : (cuts58309.take 1).map (fun c => (7646609409-1+2*2^10*c.k,113563597810719+c.lower,113563986016416+c.upper)) = pointBounds58309 := by
 decide +kernel
def cuts58310 : List PrefixCut := [⟨64,214157512,214157638⟩]
theorem checked58310 : checkPrefixCuts (2^48) 7646740481 10 Manual.Count131072.C058310.packed 64 cuts58310 = true := by
 decide +kernel
def cuts58311 : List PrefixCut := [⟨10,32870533,32870552⟩,
⟨64,210841044,210841167⟩]
theorem checked58311 : checkPrefixCuts (2^48) 7646871553 10 Manual.Count131072.C058311.packed 64 cuts58311 = true := by
 decide +kernel
def pointBounds58311 : List (Nat × Nat × Nat) := [(7646892032,113564055687037,113564443892999)]
theorem point_links_checked58311 : (cuts58311.take 1).map (fun c => (7646871553-1+2*2^10*c.k,113564022816504+c.lower,113564411022447+c.upper)) = pointBounds58311 := by
 decide +kernel
def cuts58312 : List PrefixCut := [⟨63,211389592,211389713⟩,
⟨64,215033574,215033697⟩]
theorem checked58312 : checkPrefixCuts (2^48) 7647002625 10 Manual.Count131072.C058312.packed 64 cuts58312 = true := by
 decide +kernel
def pointBounds58312 : List (Nat × Nat × Nat) := [(7647131648,113564445047140,113564833253327)]
theorem point_links_checked58312 : (cuts58312.take 1).map (fun c => (7647002625-1+2*2^10*c.k,113564233657548+c.lower,113564621863614+c.upper)) = pointBounds58312 := by
 decide +kernel
def cuts58313 : List PrefixCut := [⟨64,211606786,211606910⟩]
theorem checked58313 : checkPrefixCuts (2^48) 7647133697 10 Manual.Count131072.C058313.packed 64 cuts58313 = true := by
 decide +kernel
def cuts58314 : List PrefixCut := [⟨52,174281178,174281275⟩,
⟨64,212560138,212560257⟩]
theorem checked58314 : checkPrefixCuts (2^48) 7647264769 10 Manual.Count131072.C058314.packed 64 cuts58314 = true := by
 decide +kernel
def pointBounds58314 : List (Nat × Nat × Nat) := [(7647371264,113564834579086,113565222785496)]
theorem point_links_checked58314 : (cuts58314.take 1).map (fun c => (7647264769-1+2*2^10*c.k,113564660297908+c.lower,113565048504221+c.upper)) = pointBounds58314 := by
 decide +kernel
def cuts58315 : List PrefixCut := [⟨64,211341866,211341985⟩]
theorem checked58315 : checkPrefixCuts (2^48) 7647395841 10 Manual.Count131072.C058315.packed 64 cuts58315 = true := by
 decide +kernel
def cuts58316 : List PrefixCut := [⟨41,137580089,137580165⟩,
⟨64,210859808,210859927⟩]
theorem checked58316 : checkPrefixCuts (2^48) 7647526913 10 Manual.Count131072.C058316.packed 64 cuts58316 = true := by
 decide +kernel
def pointBounds58316 : List (Nat × Nat × Nat) := [(7647610880,113565221780001,113565609986628)]
theorem point_links_checked58316 : (cuts58316.take 1).map (fun c => (7647526913-1+2*2^10*c.k,113565084199912+c.lower,113565472406463+c.upper)) = pointBounds58316 := by
 decide +kernel
def cuts58317 : List PrefixCut := [⟨64,212254763,212254884⟩]
theorem checked58317 : checkPrefixCuts (2^48) 7647657985 10 Manual.Count131072.C058317.packed 64 cuts58317 = true := by
 decide +kernel
def cuts58318 : List PrefixCut := [⟨30,98857133,98857191⟩,
⟨64,211441424,211441547⟩]
theorem checked58318 : checkPrefixCuts (2^48) 7647789057 10 Manual.Count131072.C058318.packed 64 cuts58318 = true := by
 decide +kernel
def pointBounds58318 : List (Nat × Nat × Nat) := [(7647850496,113565606171616,113565994378465)]
theorem point_links_checked58318 : (cuts58318.take 1).map (fun c => (7647789057-1+2*2^10*c.k,113565507314483+c.lower,113565895521274+c.upper)) = pointBounds58318 := by
 decide +kernel
def cuts58319 : List PrefixCut := [⟨64,211106575,211106692⟩]
theorem checked58319 : checkPrefixCuts (2^48) 7647920129 10 Manual.Count131072.C058319.packed 64 cuts58319 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000259
