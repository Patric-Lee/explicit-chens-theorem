import PlattAssemblyKernel
import PlattCertificates.Count131072.C043584
import PlattCertificates.Count131072.C043585
import PlattCertificates.Count131072.C043586
import PlattCertificates.Count131072.C043587
import PlattCertificates.Count131072.C043588
import PlattCertificates.Count131072.C043589
import PlattCertificates.Count131072.C043590
import PlattCertificates.Count131072.C043591
import PlattCertificates.Count131072.C043592
import PlattCertificates.Count131072.C043593
import PlattCertificates.Count131072.C043594
import PlattCertificates.Count131072.C043595
import PlattCertificates.Count131072.C043596
import PlattCertificates.Count131072.C043597
import PlattCertificates.Count131072.C043598
import PlattCertificates.Count131072.C043599
import PlattCertificates.Count131072.C043600
import PlattCertificates.Count131072.C043601
import PlattCertificates.Count131072.C043602
import PlattCertificates.Count131072.C043603
import PlattCertificates.Count131072.C043604
import PlattCertificates.Count131072.C043605
import PlattCertificates.Count131072.C043606
import PlattCertificates.Count131072.C043607
import PlattCertificates.Count131072.C043608
import PlattCertificates.Count131072.C043609
import PlattCertificates.Count131072.C043610
import PlattCertificates.Count131072.C043611
import PlattCertificates.Count131072.C043612
import PlattCertificates.Count131072.C043613
import PlattCertificates.Count131072.C043614
import PlattCertificates.Count131072.C043615
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000112
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43584 : List PrefixCut := [⟨64,287499659,287499826⟩]
theorem checked43584 : checkPrefixCuts (2^48) 5716574209 10 Manual.Count131072.C043584.packed 64 cuts43584 = true := by
 decide +kernel
def cuts43585 : List PrefixCut := [⟨14,62038791,62038827⟩,
⟨64,283307954,283308127⟩]
theorem checked43585 : checkPrefixCuts (2^48) 5716705281 10 Manual.Count131072.C043585.packed 64 cuts43585 = true := by
 decide +kernel
def pointBounds43585 : List (Nat × Nat × Nat) := [(5716733952,109942993170934,109943379308851)]
theorem point_links_checked43585 : (cuts43585.take 1).map (fun c => (5716705281-1+2*2^10*c.k,109942931132143+c.lower,109943317270024+c.upper)) = pointBounds43585 := by
 decide +kernel
def cuts43586 : List PrefixCut := [⟨38,170208151,170208246⟩,
⟨64,287880338,287880504⟩]
theorem checked43586 : checkPrefixCuts (2^48) 5716836353 10 Manual.Count131072.C043586.packed 64 cuts43586 = true := by
 decide +kernel
def pointBounds43586 : List (Nat × Nat × Nat) := [(5716914176,109943384648248,109943770786397)]
theorem point_links_checked43586 : (cuts43586.take 1).map (fun c => (5716836353-1+2*2^10*c.k,109943214440097+c.lower,109943600578151+c.upper)) = pointBounds43586 := by
 decide +kernel
def cuts43587 : List PrefixCut := [⟨62,281473369,281473530⟩,
⟨64,290532405,290532571⟩]
theorem checked43587 : checkPrefixCuts (2^48) 5716967425 10 Manual.Count131072.C043587.packed 64 cuts43587 = true := by
 decide +kernel
def pointBounds43587 : List (Nat × Nat × Nat) := [(5717094400,109943783793804,109944169932185)]
theorem point_links_checked43587 : (cuts43587.take 1).map (fun c => (5716967425-1+2*2^10*c.k,109943502320435+c.lower,109943888458655+c.upper)) = pointBounds43587 := by
 decide +kernel
def cuts43588 : List PrefixCut := [⟨64,285700914,285701084⟩]
theorem checked43588 : checkPrefixCuts (2^48) 5717098497 10 Manual.Count131072.C043588.packed 64 cuts43588 = true := by
 decide +kernel
def cuts43589 : List PrefixCut := [⟨22,97283516,97283571⟩,
⟨64,284365049,284365215⟩]
theorem checked43589 : checkPrefixCuts (2^48) 5717229569 10 Manual.Count131072.C043589.packed 64 cuts43589 = true := by
 decide +kernel
def pointBounds43589 : List (Nat × Nat × Nat) := [(5717274624,109944175837270,109944561975881)]
theorem point_links_checked43589 : (cuts43589.take 1).map (fun c => (5717229569-1+2*2^10*c.k,109944078553754+c.lower,109944464692310+c.upper)) = pointBounds43589 := by
 decide +kernel
def cuts43590 : List PrefixCut := [⟨46,207411080,207411202⟩,
⟨64,288690876,288691046⟩]
theorem checked43590 : checkPrefixCuts (2^48) 5717360641 10 Manual.Count131072.C043590.packed 64 cuts43590 = true := by
 decide +kernel
def pointBounds43590 : List (Nat × Nat × Nat) := [(5717454848,109944570329883,109944956468727)]
theorem point_links_checked43590 : (cuts43590.take 1).map (fun c => (5717360641-1+2*2^10*c.k,109944362918803+c.lower,109944749057525+c.upper)) = pointBounds43590 := by
 decide +kernel
def cuts43591 : List PrefixCut := [⟨64,289225788,289225956⟩]
theorem checked43591 : checkPrefixCuts (2^48) 5717491713 10 Manual.Count131072.C043591.packed 64 cuts43591 = true := by
 decide +kernel
def cuts43592 : List PrefixCut := [⟨6,26731513,26731527⟩,
⟨64,287053077,287053241⟩]
theorem checked43592 : checkPrefixCuts (2^48) 5717622785 10 Manual.Count131072.C043592.packed 64 cuts43592 = true := by
 decide +kernel
def pointBounds43592 : List (Nat × Nat × Nat) := [(5717635072,109944967566980,109945353706054)]
theorem point_links_checked43592 : (cuts43592.take 1).map (fun c => (5717622785-1+2*2^10*c.k,109944940835467+c.lower,109945326974527+c.upper)) = pointBounds43592 := by
 decide +kernel
def cuts43593 : List PrefixCut := [⟨30,135179992,135180071⟩,
⟨64,289507895,289508065⟩]
theorem checked43593 : checkPrefixCuts (2^48) 5717753857 10 Manual.Count131072.C043593.packed 64 cuts43593 = true := by
 decide +kernel
def pointBounds43593 : List (Nat × Nat × Nat) := [(5717815296,109945363068536,109945749207839)]
theorem point_links_checked43593 : (cuts43593.take 1).map (fun c => (5717753857-1+2*2^10*c.k,109945227888544+c.lower,109945614027768+c.upper)) = pointBounds43593 := by
 decide +kernel
def cuts43594 : List PrefixCut := [⟨54,244360986,244361123⟩,
⟨64,289698186,289698351⟩]
theorem checked43594 : checkPrefixCuts (2^48) 5717884929 10 Manual.Count131072.C043594.packed 64 cuts43594 = true := by
 decide +kernel
def pointBounds43594 : List (Nat × Nat × Nat) := [(5717995520,109945761757425,109946147896956)]
theorem point_links_checked43594 : (cuts43594.take 1).map (fun c => (5717884929-1+2*2^10*c.k,109945517396439+c.lower,109945903535833+c.upper)) = pointBounds43594 := by
 decide +kernel
def cuts43595 : List PrefixCut := [⟨64,288214774,288214935⟩]
theorem checked43595 : checkPrefixCuts (2^48) 5718016001 10 Manual.Count131072.C043595.packed 64 cuts43595 = true := by
 decide +kernel
def cuts43596 : List PrefixCut := [⟨14,63499892,63499929⟩,
⟨64,288897289,288897464⟩]
theorem checked43596 : checkPrefixCuts (2^48) 5718147073 10 Manual.Count131072.C043596.packed 64 cuts43596 = true := by
 decide +kernel
def pointBounds43596 : List (Nat × Nat × Nat) := [(5718175744,109946158809291,109946544949048)]
theorem point_links_checked43596 : (cuts43596.take 1).map (fun c => (5718147073-1+2*2^10*c.k,109946095309399+c.lower,109946481449119+c.upper)) = pointBounds43596 := by
 decide +kernel
def cuts43597 : List PrefixCut := [⟨38,169820650,169820749⟩,
⟨64,290613443,290613610⟩]
theorem checked43597 : checkPrefixCuts (2^48) 5718278145 10 Manual.Count131072.C043597.packed 64 cuts43597 = true := by
 decide +kernel
def pointBounds43597 : List (Nat × Nat × Nat) := [(5718355968,109946554027338,109946940167332)]
theorem point_links_checked43597 : (cuts43597.take 1).map (fun c => (5718278145-1+2*2^10*c.k,109946384206688+c.lower,109946770346583+c.upper)) = pointBounds43597 := by
 decide +kernel
def cuts43598 : List PrefixCut := [⟨62,275987954,275988116⟩,
⟨64,284946262,284946430⟩]
theorem checked43598 : checkPrefixCuts (2^48) 5718409217 10 Manual.Count131072.C043598.packed 64 cuts43598 = true := by
 decide +kernel
def pointBounds43598 : List (Nat × Nat × Nat) := [(5718536192,109946950808085,109947336948309)]
theorem point_links_checked43598 : (cuts43598.take 1).map (fun c => (5718409217-1+2*2^10*c.k,109946674820131+c.lower,109947060960193+c.upper)) = pointBounds43598 := by
 decide +kernel
def cuts43599 : List PrefixCut := [⟨64,288286808,288286970⟩]
theorem checked43599 : checkPrefixCuts (2^48) 5718540289 10 Manual.Count131072.C043599.packed 64 cuts43599 = true := by
 decide +kernel
def cuts43600 : List PrefixCut := [⟨22,98292619,98292676⟩,
⟨64,286163732,286163904⟩]
theorem checked43600 : checkPrefixCuts (2^48) 5718671361 10 Manual.Count131072.C043600.packed 64 cuts43600 = true := by
 decide +kernel
def pointBounds43600 : List (Nat × Nat × Nat) := [(5718716416,109947346345820,109947732486269)]
theorem point_links_checked43600 : (cuts43600.take 1).map (fun c => (5718671361-1+2*2^10*c.k,109947248053201+c.lower,109947634193593+c.upper)) = pointBounds43600 := by
 decide +kernel
def cuts43601 : List PrefixCut := [⟨46,205143955,205144078⟩,
⟨64,285468109,285468280⟩]
theorem checked43601 : checkPrefixCuts (2^48) 5718802433 10 Manual.Count131072.C043601.packed 64 cuts43601 = true := by
 decide +kernel
def pointBounds43601 : List (Nat × Nat × Nat) := [(5718896640,109947739360888,109948125501575)]
theorem point_links_checked43601 : (cuts43601.take 1).map (fun c => (5718802433-1+2*2^10*c.k,109947534216933+c.lower,109947920357497+c.upper)) = pointBounds43601 := by
 decide +kernel
def cuts43602 : List PrefixCut := [⟨64,286839640,286839809⟩]
theorem checked43602 : checkPrefixCuts (2^48) 5718933505 10 Manual.Count131072.C043602.packed 64 cuts43602 = true := by
 decide +kernel
def cuts43603 : List PrefixCut := [⟨6,27709111,27709127⟩,
⟨64,289638399,289638563⟩]
theorem checked43603 : checkPrefixCuts (2^48) 5719064577 10 Manual.Count131072.C043603.packed 64 cuts43603 = true := by
 decide +kernel
def pointBounds43603 : List (Nat × Nat × Nat) := [(5719076864,109948134233793,109948520374713)]
theorem point_links_checked43603 : (cuts43603.take 1).map (fun c => (5719064577-1+2*2^10*c.k,109948106524682+c.lower,109948492665586+c.upper)) = pointBounds43603 := by
 decide +kernel
def cuts43604 : List PrefixCut := [⟨30,136474729,136474808⟩,
⟨64,286383600,286383768⟩]
theorem checked43604 : checkPrefixCuts (2^48) 5719195649 10 Manual.Count131072.C043604.packed 64 cuts43604 = true := by
 decide +kernel
def pointBounds43604 : List (Nat × Nat × Nat) := [(5719257088,109948532637810,109948918778957)]
theorem point_links_checked43604 : (cuts43604.take 1).map (fun c => (5719195649-1+2*2^10*c.k,109948396163081+c.lower,109948782304149+c.upper)) = pointBounds43604 := by
 decide +kernel
def cuts43605 : List PrefixCut := [⟨54,243954862,243955007⟩,
⟨64,288345576,288345746⟩]
theorem checked43605 : checkPrefixCuts (2^48) 5719326721 10 Manual.Count131072.C043605.packed 64 cuts43605 = true := by
 decide +kernel
def pointBounds43605 : List (Nat × Nat × Nat) := [(5719437312,109948926501543,109949312642924)]
theorem point_links_checked43605 : (cuts43605.take 1).map (fun c => (5719326721-1+2*2^10*c.k,109948682546681+c.lower,109949068687917+c.upper)) = pointBounds43605 := by
 decide +kernel
def cuts43606 : List PrefixCut := [⟨64,290110628,290110802⟩]
theorem checked43606 : checkPrefixCuts (2^48) 5719457793 10 Manual.Count131072.C043606.packed 64 cuts43606 = true := by
 decide +kernel
def cuts43607 : List PrefixCut := [⟨14,65403163,65403204⟩,
⟨64,292416963,292417137⟩]
theorem checked43607 : checkPrefixCuts (2^48) 5719588865 10 Manual.Count131072.C043607.packed 64 cuts43607 = true := by
 decide +kernel
def pointBounds43607 : List (Nat × Nat × Nat) := [(5719617536,109949326406048,109949712547669)]
theorem point_links_checked43607 : (cuts43607.take 1).map (fun c => (5719588865-1+2*2^10*c.k,109949261002885+c.lower,109949647144465+c.upper)) = pointBounds43607 := by
 decide +kernel
def cuts43608 : List PrefixCut := [⟨38,171254171,171254272⟩,
⟨64,286750996,286751173⟩]
theorem checked43608 : checkPrefixCuts (2^48) 5719719937 10 Manual.Count131072.C043608.packed 64 cuts43608 = true := by
 decide +kernel
def pointBounds43608 : List (Nat × Nat × Nat) := [(5719797760,109949724674019,109950110815874)]
theorem point_links_checked43608 : (cuts43608.take 1).map (fun c => (5719719937-1+2*2^10*c.k,109949553419848+c.lower,109949939561602+c.upper)) = pointBounds43608 := by
 decide +kernel
def cuts43609 : List PrefixCut := [⟨62,279904398,279904563⟩,
⟨64,289352539,289352710⟩]
theorem checked43609 : checkPrefixCuts (2^48) 5719851009 10 Manual.Count131072.C043609.packed 64 cuts43609 = true := by
 decide +kernel
def pointBounds43609 : List (Nat × Nat × Nat) := [(5719977984,109950120075242,109950506217338)]
theorem point_links_checked43609 : (cuts43609.take 1).map (fun c => (5719851009-1+2*2^10*c.k,109949840170844+c.lower,109950226312775+c.upper)) = pointBounds43609 := by
 decide +kernel
def cuts43610 : List PrefixCut := [⟨64,286737863,286738028⟩]
theorem checked43610 : checkPrefixCuts (2^48) 5719982081 10 Manual.Count131072.C043610.packed 64 cuts43610 = true := by
 decide +kernel
def cuts43611 : List PrefixCut := [⟨22,92904198,92904253⟩,
⟨64,278169197,278169361⟩]
theorem checked43611 : checkPrefixCuts (2^48) 5720113153 10 Manual.Count131072.C043611.packed 64 cuts43611 = true := by
 decide +kernel
def pointBounds43611 : List (Nat × Nat × Nat) := [(5720158208,109950509165444,109950895307766)]
theorem point_links_checked43611 : (cuts43611.take 1).map (fun c => (5720113153-1+2*2^10*c.k,109950416261246+c.lower,109950802403513+c.upper)) = pointBounds43611 := by
 decide +kernel
def cuts43612 : List PrefixCut := [⟨46,204550966,204551081⟩,
⟨64,283919967,283920129⟩]
theorem checked43612 : checkPrefixCuts (2^48) 5720244225 10 Manual.Count131072.C043612.packed 64 cuts43612 = true := by
 decide +kernel
def pointBounds43612 : List (Nat × Nat × Nat) := [(5720338432,109950898981409,109951285123955)]
theorem point_links_checked43612 : (cuts43612.take 1).map (fun c => (5720244225-1+2*2^10*c.k,109950694430443+c.lower,109951080572874+c.upper)) = pointBounds43612 := by
 decide +kernel
def cuts43613 : List PrefixCut := [⟨64,282929358,282929521⟩]
theorem checked43613 : checkPrefixCuts (2^48) 5720375297 10 Manual.Count131072.C043613.packed 64 cuts43613 = true := by
 decide +kernel
def cuts43614 : List PrefixCut := [⟨6,26816448,26816462⟩,
⟨64,284694230,284694395⟩]
theorem checked43614 : checkPrefixCuts (2^48) 5720506369 10 Manual.Count131072.C043614.packed 64 cuts43614 = true := by
 decide +kernel
def pointBounds43614 : List (Nat × Nat × Nat) := [(5720518656,109951288096216,109951674238986)]
theorem point_links_checked43614 : (cuts43614.take 1).map (fun c => (5720506369-1+2*2^10*c.k,109951261279768+c.lower,109951647422524+c.upper)) = pointBounds43614 := by
 decide +kernel
def cuts43615 : List PrefixCut := [⟨30,132454880,132454954⟩,
⟨64,286409775,286409927⟩]
theorem checked43615 : checkPrefixCuts (2^48) 5720637441 10 Manual.Count131072.C043615.packed 64 cuts43615 = true := by
 decide +kernel
def pointBounds43615 : List (Nat × Nat × Nat) := [(5720698880,109951678428878,109952064571873)]
theorem point_links_checked43615 : (cuts43615.take 1).map (fun c => (5720637441-1+2*2^10*c.k,109951545973998+c.lower,109951932116919+c.upper)) = pointBounds43615 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000112
