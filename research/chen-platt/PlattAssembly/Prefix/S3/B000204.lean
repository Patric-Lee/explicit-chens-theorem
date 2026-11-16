import PlattAssemblyKernel
import PlattCertificates.Count131072.C026528
import PlattCertificates.Count131072.C026529
import PlattCertificates.Count131072.C026530
import PlattCertificates.Count131072.C026531
import PlattCertificates.Count131072.C026532
import PlattCertificates.Count131072.C026533
import PlattCertificates.Count131072.C026534
import PlattCertificates.Count131072.C026535
import PlattCertificates.Count131072.C026536
import PlattCertificates.Count131072.C026537
import PlattCertificates.Count131072.C026538
import PlattCertificates.Count131072.C026539
import PlattCertificates.Count131072.C026540
import PlattCertificates.Count131072.C026541
import PlattCertificates.Count131072.C026542
import PlattCertificates.Count131072.C026543
import PlattCertificates.Count131072.C026544
import PlattCertificates.Count131072.C026545
import PlattCertificates.Count131072.C026546
import PlattCertificates.Count131072.C026547
import PlattCertificates.Count131072.C026548
import PlattCertificates.Count131072.C026549
import PlattCertificates.Count131072.C026550
import PlattCertificates.Count131072.C026551
import PlattCertificates.Count131072.C026552
import PlattCertificates.Count131072.C026553
import PlattCertificates.Count131072.C026554
import PlattCertificates.Count131072.C026555
import PlattCertificates.Count131072.C026556
import PlattCertificates.Count131072.C026557
import PlattCertificates.Count131072.C026558
import PlattCertificates.Count131072.C026559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000204
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26528 : List PrefixCut := [⟨66,247186983,247187122⟩,
⟨128,479410619,479410891⟩]
theorem checked26528 : checkPrefixCuts (2^48) 3481010177 9 Manual.Count131072.C026528.packed 128 cuts26528 = true := by
 decide +kernel
def pointBounds26528 : List (Nat × Nat × Nat) := [(3481077760,103658471271755,103658853714169)]
theorem point_links_checked26528 : (cuts26528.take 1).map (fun c => (3481010177-1+2*2^9*c.k,103658224084772+c.lower,103658606527047+c.upper)) = pointBounds26528 := by
 decide +kernel
def cuts26529 : List PrefixCut := [⟨45,165028192,165028286⟩,
⟨128,476400889,476401153⟩]
theorem checked26529 : checkPrefixCuts (2^48) 3481141249 9 Manual.Count131072.C026529.packed 128 cuts26529 = true := by
 decide +kernel
def pointBounds26529 : List (Nat × Nat × Nat) := [(3481187328,103658868523583,103659250966224)]
theorem point_links_checked26529 : (cuts26529.take 1).map (fun c => (3481141249-1+2*2^9*c.k,103658703495391+c.lower,103659085937938+c.upper)) = pointBounds26529 := by
 decide +kernel
def cuts26530 : List PrefixCut := [⟨24,89181682,89181734⟩,
⟨128,485195872,485196142⟩]
theorem checked26530 : checkPrefixCuts (2^48) 3481272321 9 Manual.Count131072.C026530.packed 128 cuts26530 = true := by
 decide +kernel
def pointBounds26530 : List (Nat × Nat × Nat) := [(3481296896,103659269077962,103659651520825)]
theorem point_links_checked26530 : (cuts26530.take 1).map (fun c => (3481272321-1+2*2^9*c.k,103659179896280+c.lower,103659562339091+c.upper)) = pointBounds26530 := by
 decide +kernel
def cuts26531 : List PrefixCut := [⟨3,11885090,11885096⟩,
⟨110,422277890,422278120⟩,
⟨128,490190342,490190610⟩]
theorem checked26531 : checkPrefixCuts (2^48) 3481403393 9 Manual.Count131072.C026531.packed 128 cuts26531 = true := by
 decide +kernel
def pointBounds26531 : List (Nat × Nat × Nat) := [(3481406464,103659676977242,103660059420329),(3481516032,103660087370042,103660469813353)]
theorem point_links_checked26531 : (cuts26531.take 2).map (fun c => (3481403393-1+2*2^9*c.k,103659665092152+c.lower,103660047535233+c.upper)) = pointBounds26531 := by
 decide +kernel
def cuts26532 : List PrefixCut := [⟨89,330825508,330825696⟩,
⟨128,476508864,476509136⟩]
theorem checked26532 : checkPrefixCuts (2^48) 3481534465 9 Manual.Count131072.C026532.packed 128 cuts26532 = true := by
 decide +kernel
def pointBounds26532 : List (Nat × Nat × Nat) := [(3481625600,103660486108002,103660868551539)]
theorem point_links_checked26532 : (cuts26532.take 1).map (fun c => (3481534465-1+2*2^9*c.k,103660155282494+c.lower,103660537725843+c.upper)) = pointBounds26532 := by
 decide +kernel
def cuts26533 : List PrefixCut := [⟨68,254497209,254497349⟩,
⟨128,481341449,481341720⟩]
theorem checked26533 : checkPrefixCuts (2^48) 3481665537 9 Manual.Count131072.C026533.packed 128 cuts26533 = true := by
 decide +kernel
def pointBounds26533 : List (Nat × Nat × Nat) := [(3481735168,103660886288567,103661268732328)]
theorem point_links_checked26533 : (cuts26533.take 1).map (fun c => (3481665537-1+2*2^9*c.k,103660631791358+c.lower,103661014234979+c.upper)) = pointBounds26533 := by
 decide +kernel
def cuts26534 : List PrefixCut := [⟨47,174293843,174293942⟩,
⟨128,480029908,480030177⟩]
theorem checked26534 : checkPrefixCuts (2^48) 3481796609 9 Manual.Count131072.C026534.packed 128 cuts26534 = true := by
 decide +kernel
def pointBounds26534 : List (Nat × Nat × Nat) := [(3481844736,103661287426650,103661669870641)]
theorem point_links_checked26534 : (cuts26534.take 1).map (fun c => (3481796609-1+2*2^9*c.k,103661113132807+c.lower,103661495576699+c.upper)) = pointBounds26534 := by
 decide +kernel
def cuts26535 : List PrefixCut := [⟨26,99835549,99835606⟩,
⟨128,480011879,480012157⟩]
theorem checked26535 : checkPrefixCuts (2^48) 3481927681 9 Manual.Count131072.C026535.packed 128 cuts26535 = true := by
 decide +kernel
def pointBounds26535 : List (Nat × Nat × Nat) := [(3481954304,103661692998264,103662075442482)]
theorem point_links_checked26535 : (cuts26535.take 1).map (fun c => (3481927681-1+2*2^9*c.k,103661593162715+c.lower,103661975606876+c.upper)) = pointBounds26535 := by
 decide +kernel
def cuts26536 : List PrefixCut := [⟨5,17945527,17945537⟩,
⟨112,421551593,421551823⟩,
⟨128,481448784,481449046⟩]
theorem checked26536 : checkPrefixCuts (2^48) 3482058753 9 Manual.Count131072.C026536.packed 128 cuts26536 = true := by
 decide +kernel
def pointBounds26536 : List (Nat × Nat × Nat) := [(3482063872,103662091120121,103662473564570),(3482173440,103662494726187,103662877170856)]
theorem point_links_checked26536 : (cuts26536.take 2).map (fun c => (3482058753-1+2*2^9*c.k,103662073174594+c.lower,103662455619033+c.upper)) = pointBounds26536 := by
 decide +kernel
def cuts26537 : List PrefixCut := [⟨91,342968648,342968834⟩,
⟨128,485148832,485149096⟩]
theorem checked26537 : checkPrefixCuts (2^48) 3482189825 9 Manual.Count131072.C026537.packed 128 cuts26537 = true := by
 decide +kernel
def pointBounds26537 : List (Nat × Nat × Nat) := [(3482283008,103662897592026,103663280036913)]
theorem point_links_checked26537 : (cuts26537.take 1).map (fun c => (3482189825-1+2*2^9*c.k,103662554623378+c.lower,103662937068079+c.upper)) = pointBounds26537 := by
 decide +kernel
def cuts26538 : List PrefixCut := [⟨70,266573548,266573695⟩,
⟨128,477937025,477937291⟩]
theorem checked26538 : checkPrefixCuts (2^48) 3482320897 9 Manual.Count131072.C026538.packed 128 cuts26538 = true := by
 decide +kernel
def pointBounds26538 : List (Nat × Nat × Nat) := [(3482392576,103663306345758,103663688790870)]
theorem point_links_checked26538 : (cuts26538.take 1).map (fun c => (3482320897-1+2*2^9*c.k,103663039772210+c.lower,103663422217175+c.upper)) = pointBounds26538 := by
 decide +kernel
def cuts26539 : List PrefixCut := [⟨49,179999652,179999754⟩,
⟨128,474766706,474766974⟩]
theorem checked26539 : checkPrefixCuts (2^48) 3482451969 9 Manual.Count131072.C026539.packed 128 cuts26539 = true := by
 decide +kernel
def pointBounds26539 : List (Nat × Nat × Nat) := [(3482502144,103663697708887,103664080154220)]
theorem point_links_checked26539 : (cuts26539.take 1).map (fun c => (3482451969-1+2*2^9*c.k,103663517709235+c.lower,103663900154466+c.upper)) = pointBounds26539 := by
 decide +kernel
def cuts26540 : List PrefixCut := [⟨28,106444242,106444302⟩,
⟨128,482992708,482992980⟩]
theorem checked26540 : checkPrefixCuts (2^48) 3482583041 9 Manual.Count131072.C026540.packed 128 cuts26540 = true := by
 decide +kernel
def pointBounds26540 : List (Nat × Nat × Nat) := [(3482611712,103664098920183,103664481365742)]
theorem point_links_checked26540 : (cuts26540.take 1).map (fun c => (3482583041-1+2*2^9*c.k,103663992475941+c.lower,103664374921440+c.upper)) = pointBounds26540 := by
 decide +kernel
def cuts26541 : List PrefixCut := [⟨7,24892707,24892722⟩,
⟨114,427695236,427695471⟩,
⟨128,480145910,480146175⟩]
theorem checked26541 : checkPrefixCuts (2^48) 3482714113 9 Manual.Count131072.C026541.packed 128 cuts26541 = true := by
 decide +kernel
def pointBounds26541 : List (Nat × Nat × Nat) := [(3482721280,103664500361356,103664882807142),(3482830848,103664903163885,103665285609891)]
theorem point_links_checked26541 : (cuts26541.take 2).map (fun c => (3482714113-1+2*2^9*c.k,103664475468649+c.lower,103664857914420+c.upper)) = pointBounds26541 := by
 decide +kernel
def cuts26542 : List PrefixCut := [⟨93,352925264,352925455⟩,
⟨128,487886126,487886391⟩]
theorem checked26542 : checkPrefixCuts (2^48) 3482845185 9 Manual.Count131072.C026542.packed 128 cuts26542 = true := by
 decide +kernel
def pointBounds26542 : List (Nat × Nat × Nat) := [(3482940416,103665308539823,103665690986050)]
theorem point_links_checked26542 : (cuts26542.take 1).map (fun c => (3482845185-1+2*2^9*c.k,103664955614559+c.lower,103665338060595+c.upper)) = pointBounds26542 := by
 decide +kernel
def cuts26543 : List PrefixCut := [⟨72,275008762,275008911⟩,
⟨128,482776662,482776926⟩]
theorem checked26543 : checkPrefixCuts (2^48) 3482976257 9 Manual.Count131072.C026543.packed 128 cuts26543 = true := by
 decide +kernel
def pointBounds26543 : List (Nat × Nat × Nat) := [(3483049984,103665718509447,103666100955897)]
theorem point_links_checked26543 : (cuts26543.take 1).map (fun c => (3482976257-1+2*2^9*c.k,103665443500685+c.lower,103665825946986+c.upper)) = pointBounds26543 := by
 decide +kernel
def cuts26544 : List PrefixCut := [⟨51,188450830,188450939⟩,
⟨128,482273477,482273751⟩]
theorem checked26544 : checkPrefixCuts (2^48) 3483107329 9 Manual.Count131072.C026544.packed 128 cuts26544 = true := by
 decide +kernel
def pointBounds26544 : List (Nat × Nat × Nat) := [(3483159552,103666114728177,103666497174851)]
theorem point_links_checked26544 : (cuts26544.take 1).map (fun c => (3483107329-1+2*2^9*c.k,103665926277347+c.lower,103666308723912+c.upper)) = pointBounds26544 := by
 decide +kernel
def cuts26545 : List PrefixCut := [⟨30,111595896,111595961⟩,
⟨128,479669534,479669800⟩]
theorem checked26545 : checkPrefixCuts (2^48) 3483238401 9 Manual.Count131072.C026545.packed 128 cuts26545 = true := by
 decide +kernel
def pointBounds26545 : List (Nat × Nat × Nat) := [(3483269120,103666520146720,103666902593624)]
theorem point_links_checked26545 : (cuts26545.take 1).map (fun c => (3483238401-1+2*2^9*c.k,103666408550824+c.lower,103666790997663+c.upper)) = pointBounds26545 := by
 decide +kernel
def cuts26546 : List PrefixCut := [⟨9,33776590,33776609⟩,
⟨116,435452600,435452845⟩,
⟨128,479328336,479328604⟩]
theorem checked26546 : checkPrefixCuts (2^48) 3483369473 9 Manual.Count131072.C026546.packed 128 cuts26546 = true := by
 decide +kernel
def pointBounds26546 : List (Nat × Nat × Nat) := [(3483378688,103666921996948,103667304444072),(3483488256,103667323672958,103667706120308)]
theorem point_links_checked26546 : (cuts26546.take 2).map (fun c => (3483369473-1+2*2^9*c.k,103666888220358+c.lower,103667270667463+c.upper)) = pointBounds26546 := by
 decide +kernel
def cuts26547 : List PrefixCut := [⟨95,358595669,358595871⟩,
⟨128,478744769,478745042⟩]
theorem checked26547 : checkPrefixCuts (2^48) 3483500545 9 Manual.Count131072.C026547.packed 128 cuts26547 = true := by
 decide +kernel
def pointBounds26547 : List (Nat × Nat × Nat) := [(3483597824,103667726144363,103668108591938)]
theorem point_links_checked26547 : (cuts26547.take 1).map (fun c => (3483500545-1+2*2^9*c.k,103667367548694+c.lower,103667749996067+c.upper)) = pointBounds26547 := by
 decide +kernel
def cuts26548 : List PrefixCut := [⟨74,276411353,276411509⟩,
⟨128,478888321,478888588⟩]
theorem checked26548 : checkPrefixCuts (2^48) 3483631617 9 Manual.Count131072.C026548.packed 128 cuts26548 = true := by
 decide +kernel
def pointBounds26548 : List (Nat × Nat × Nat) := [(3483707392,103668122704816,103668505152618)]
theorem point_links_checked26548 : (cuts26548.take 1).map (fun c => (3483631617-1+2*2^9*c.k,103667846293463+c.lower,103668228741109+c.upper)) = pointBounds26548 := by
 decide +kernel
def cuts26549 : List PrefixCut := [⟨53,193990227,193990338⟩,
⟨128,474345665,474345932⟩]
theorem checked26549 : checkPrefixCuts (2^48) 3483762689 9 Manual.Count131072.C026549.packed 128 cuts26549 = true := by
 decide +kernel
def pointBounds26549 : List (Nat × Nat × Nat) := [(3483816960,103668519172011,103668901620035)]
theorem point_links_checked26549 : (cuts26549.take 1).map (fun c => (3483762689-1+2*2^9*c.k,103668325181784+c.lower,103668707629697+c.upper)) = pointBounds26549 := by
 decide +kernel
def cuts26550 : List PrefixCut := [⟨32,121512390,121512458⟩,
⟨128,485396406,485396677⟩]
theorem checked26550 : checkPrefixCuts (2^48) 3483893761 9 Manual.Count131072.C026550.packed 128 cuts26550 = true := by
 decide +kernel
def pointBounds26550 : List (Nat × Nat × Nat) := [(3483926528,103668921039839,103669303488087)]
theorem point_links_checked26550 : (cuts26550.take 1).map (fun c => (3483893761-1+2*2^9*c.k,103668799527449+c.lower,103669181975629+c.upper)) = pointBounds26550 := by
 decide +kernel
def cuts26551 : List PrefixCut := [⟨11,43545822,43545846⟩,
⟨118,447084999,447085247⟩,
⟨128,483681616,483681885⟩]
theorem checked26551 : checkPrefixCuts (2^48) 3484024833 9 Manual.Count131072.C026551.packed 128 cuts26551 = true := by
 decide +kernel
def pointBounds26551 : List (Nat × Nat × Nat) := [(3484036096,103669328469677,103669710918152),(3484145664,103669732008854,103670114457553)]
theorem point_links_checked26551 : (cuts26551.take 2).map (fun c => (3484024833-1+2*2^9*c.k,103669284923855+c.lower,103669667372306+c.upper)) = pointBounds26551 := by
 decide +kernel
def cuts26552 : List PrefixCut := [⟨97,368383997,368384197⟩,
⟨128,484390454,484390719⟩]
theorem checked26552 : checkPrefixCuts (2^48) 3484155905 9 Manual.Count131072.C026552.packed 128 cuts26552 = true := by
 decide +kernel
def pointBounds26552 : List (Nat × Nat × Nat) := [(3484255232,103670136989468,103670519438388)]
theorem point_links_checked26552 : (cuts26552.take 1).map (fun c => (3484155905-1+2*2^9*c.k,103669768605471+c.lower,103670151054191+c.upper)) = pointBounds26552 := by
 decide +kernel
def cuts26553 : List PrefixCut := [⟨76,287911248,287911410⟩,
⟨128,487765070,487765343⟩]
theorem checked26553 : checkPrefixCuts (2^48) 3484286977 9 Manual.Count131072.C026553.packed 128 cuts26553 = true := by
 decide +kernel
def pointBounds26553 : List (Nat × Nat × Nat) := [(3484364800,103670540907173,103670923356320)]
theorem point_links_checked26553 : (cuts26553.take 1).map (fun c => (3484286977-1+2*2^9*c.k,103670252995925+c.lower,103670635444910+c.upper)) = pointBounds26553 := by
 decide +kernel
def cuts26554 : List PrefixCut := [⟨55,209463523,209463640⟩,
⟨128,482657634,482657903⟩]
theorem checked26554 : checkPrefixCuts (2^48) 3484418049 9 Manual.Count131072.C026554.packed 128 cuts26554 = true := by
 decide +kernel
def pointBounds26554 : List (Nat × Nat × Nat) := [(3484474368,103670950224518,103671332673893)]
theorem point_links_checked26554 : (cuts26554.take 1).map (fun c => (3484418049-1+2*2^9*c.k,103670740760995+c.lower,103671123210253+c.upper)) = pointBounds26554 := by
 decide +kernel
def cuts26555 : List PrefixCut := [⟨34,127143925,127143995⟩,
⟨128,482962550,482962820⟩]
theorem checked26555 : checkPrefixCuts (2^48) 3484549121 9 Manual.Count131072.C026555.packed 128 cuts26555 = true := by
 decide +kernel
def pointBounds26555 : List (Nat × Nat × Nat) := [(3484583936,103671350562554,103671733012151)]
theorem point_links_checked26555 : (cuts26555.take 1).map (fun c => (3484549121-1+2*2^9*c.k,103671223418629+c.lower,103671605868156+c.upper)) = pointBounds26555 := by
 decide +kernel
def cuts26556 : List PrefixCut := [⟨13,51211227,51211256⟩,
⟨120,455643524,455643774⟩,
⟨128,488760050,488760318⟩]
theorem checked26556 : checkPrefixCuts (2^48) 3484680193 9 Manual.Count131072.C026556.packed 128 cuts26556 = true := by
 decide +kernel
def pointBounds26556 : List (Nat × Nat × Nat) := [(3484693504,103671757592406,103672140042232),(3484803072,103672162024703,103672544474750)]
theorem point_links_checked26556 : (cuts26556.take 2).map (fun c => (3484680193-1+2*2^9*c.k,103671706381179+c.lower,103672088830976+c.upper)) = pointBounds26556 := by
 decide +kernel
def cuts26557 : List PrefixCut := [⟨99,372110795,372111007⟩,
⟨128,479291552,479291825⟩]
theorem checked26557 : checkPrefixCuts (2^48) 3484811265 9 Manual.Count131072.C026557.packed 128 cuts26557 = true := by
 decide +kernel
def pointBounds26557 : List (Nat × Nat × Nat) := [(3484912640,103672567252024,103672949702301)]
theorem point_links_checked26557 : (cuts26557.take 1).map (fun c => (3484811265-1+2*2^9*c.k,103672195141229+c.lower,103672577591294+c.upper)) = pointBounds26557 := by
 decide +kernel
def cuts26558 : List PrefixCut := [⟨78,294964543,294964709⟩,
⟨128,485815617,485815887⟩]
theorem checked26558 : checkPrefixCuts (2^48) 3484942337 9 Manual.Count131072.C026558.packed 128 cuts26558 = true := by
 decide +kernel
def pointBounds26558 : List (Nat × Nat × Nat) := [(3485022208,103672969397324,103673351847828)]
theorem point_links_checked26558 : (cuts26558.take 1).map (fun c => (3484942337-1+2*2^9*c.k,103672674432781+c.lower,103673056883119+c.upper)) = pointBounds26558 := by
 decide +kernel
def cuts26559 : List PrefixCut := [⟨57,217096789,217096905⟩,
⟨128,483213022,483213284⟩]
theorem checked26559 : checkPrefixCuts (2^48) 3485073409 9 Manual.Count131072.C026559.packed 128 cuts26559 = true := by
 decide +kernel
def pointBounds26559 : List (Nat × Nat × Nat) := [(3485131776,103673377345187,103673759795911)]
theorem point_links_checked26559 : (cuts26559.take 1).map (fun c => (3485073409-1+2*2^9*c.k,103673160248398+c.lower,103673542699006+c.upper)) = pointBounds26559 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000204
