import PlattAssemblyKernel
import PlattCertificates.Count131072.C040608
import PlattCertificates.Count131072.C040609
import PlattCertificates.Count131072.C040610
import PlattCertificates.Count131072.C040611
import PlattCertificates.Count131072.C040612
import PlattCertificates.Count131072.C040613
import PlattCertificates.Count131072.C040614
import PlattCertificates.Count131072.C040615
import PlattCertificates.Count131072.C040616
import PlattCertificates.Count131072.C040617
import PlattCertificates.Count131072.C040618
import PlattCertificates.Count131072.C040619
import PlattCertificates.Count131072.C040620
import PlattCertificates.Count131072.C040621
import PlattCertificates.Count131072.C040622
import PlattCertificates.Count131072.C040623
import PlattCertificates.Count131072.C040624
import PlattCertificates.Count131072.C040625
import PlattCertificates.Count131072.C040626
import PlattCertificates.Count131072.C040627
import PlattCertificates.Count131072.C040628
import PlattCertificates.Count131072.C040629
import PlattCertificates.Count131072.C040630
import PlattCertificates.Count131072.C040631
import PlattCertificates.Count131072.C040632
import PlattCertificates.Count131072.C040633
import PlattCertificates.Count131072.C040634
import PlattCertificates.Count131072.C040635
import PlattCertificates.Count131072.C040636
import PlattCertificates.Count131072.C040637
import PlattCertificates.Count131072.C040638
import PlattCertificates.Count131072.C040639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40608 : List PrefixCut := [⟨21,101407626,101407686⟩,
⟨64,310667287,310667467⟩]
theorem checked40608 : checkPrefixCuts (2^48) 5326503937 10 Manual.Count131072.C040608.packed 64 cuts40608 = true := by
 decide +kernel
def pointBounds40608 : List (Nat × Nat × Nat) := [(5326546944,109055843466983,109056229085090)]
theorem point_links_checked40608 : (cuts40608.take 1).map (fun c => (5326503937-1+2*2^10*c.k,109055742059357+c.lower,109056127677404+c.upper)) = pointBounds40608 := by
 decide +kernel
def cuts40609 : List PrefixCut := [⟨39,186322695,186322805⟩,
⟨64,307066355,307066536⟩]
theorem checked40609 : checkPrefixCuts (2^48) 5326635009 10 Manual.Count131072.C040609.packed 64 cuts40609 = true := by
 decide +kernel
def pointBounds40609 : List (Nat × Nat × Nat) := [(5326714880,109056239049339,109056624667676)]
theorem point_links_checked40609 : (cuts40609.take 1).map (fun c => (5326635009-1+2*2^10*c.k,109056052726644+c.lower,109056438344871+c.upper)) = pointBounds40609 := by
 decide +kernel
def cuts40610 : List PrefixCut := [⟨57,279529039,279529201⟩,
⟨64,312607115,312607297⟩]
theorem checked40610 : checkPrefixCuts (2^48) 5326766081 10 Manual.Count131072.C040610.packed 64 cuts40610 = true := by
 decide +kernel
def pointBounds40610 : List (Nat × Nat × Nat) := [(5326882816,109056639322038,109057024940608)]
theorem point_links_checked40610 : (cuts40610.take 1).map (fun c => (5326766081-1+2*2^10*c.k,109056359792999+c.lower,109056745411407+c.upper)) = pointBounds40610 := by
 decide +kernel
def cuts40611 : List PrefixCut := [⟨64,312810815,312810998⟩]
theorem checked40611 : checkPrefixCuts (2^48) 5326897153 10 Manual.Count131072.C040611.packed 64 cuts40611 = true := by
 decide +kernel
def cuts40612 : List PrefixCut := [⟨11,55005291,55005323⟩,
⟨64,312855936,312856122⟩]
theorem checked40612 : checkPrefixCuts (2^48) 5327028225 10 Manual.Count131072.C040612.packed 64 cuts40612 = true := by
 decide +kernel
def pointBounds40612 : List (Nat × Nat × Nat) := [(5327050752,109057040216220,109057425835025)]
theorem point_links_checked40612 : (cuts40612.take 1).map (fun c => (5327028225-1+2*2^10*c.k,109056985210929+c.lower,109057370829702+c.upper)) = pointBounds40612 := by
 decide +kernel
def cuts40613 : List PrefixCut := [⟨29,139543608,139543691⟩,
⟨64,305715244,305715426⟩]
theorem checked40613 : checkPrefixCuts (2^48) 5327159297 10 Manual.Count131072.C040613.packed 64 cuts40613 = true := by
 decide +kernel
def pointBounds40613 : List (Nat × Nat × Nat) := [(5327218688,109057437610473,109057823229515)]
theorem point_links_checked40613 : (cuts40613.take 1).map (fun c => (5327159297-1+2*2^10*c.k,109057298066865+c.lower,109057683685824+c.upper)) = pointBounds40613 := by
 decide +kernel
def cuts40614 : List PrefixCut := [⟨47,224711209,224711347⟩,
⟨64,306288880,306289067⟩]
theorem checked40614 : checkPrefixCuts (2^48) 5327290369 10 Manual.Count131072.C040614.packed 64 cuts40614 = true := by
 decide +kernel
def pointBounds40614 : List (Nat × Nat × Nat) := [(5327386624,109057828493318,109058214112597)]
theorem point_links_checked40614 : (cuts40614.take 1).map (fun c => (5327290369-1+2*2^10*c.k,109057603782109+c.lower,109057989401250+c.upper)) = pointBounds40614 := by
 decide +kernel
def cuts40615 : List PrefixCut := [⟨64,308923052,308923238⟩]
theorem checked40615 : checkPrefixCuts (2^48) 5327421441 10 Manual.Count131072.C040615.packed 64 cuts40615 = true := by
 decide +kernel
def cuts40616 : List PrefixCut := [⟨1,4755042,4755045⟩,
⟨64,312032621,312032806⟩]
theorem checked40616 : checkPrefixCuts (2^48) 5327552513 10 Manual.Count131072.C040616.packed 64 cuts40616 = true := by
 decide +kernel
def pointBounds40616 : List (Nat × Nat × Nat) := [(5327554560,109058223749083,109058609368600)]
theorem point_links_checked40616 : (cuts40616.take 1).map (fun c => (5327552513-1+2*2^10*c.k,109058218994041+c.lower,109058604613555+c.upper)) = pointBounds40616 := by
 decide +kernel
def cuts40617 : List PrefixCut := [⟨19,92139559,92139612⟩,
⟨64,306107815,306107995⟩]
theorem checked40617 : checkPrefixCuts (2^48) 5327683585 10 Manual.Count131072.C040617.packed 64 cuts40617 = true := by
 decide +kernel
def pointBounds40617 : List (Nat × Nat × Nat) := [(5327722496,109058623166221,109059008785973)]
theorem point_links_checked40617 : (cuts40617.take 1).map (fun c => (5327683585-1+2*2^10*c.k,109058531026662+c.lower,109058916646361+c.upper)) = pointBounds40617 := by
 decide +kernel
def cuts40618 : List PrefixCut := [⟨37,177670087,177670193⟩,
⟨64,309851202,309851388⟩]
theorem checked40618 : checkPrefixCuts (2^48) 5327814657 10 Manual.Count131072.C040618.packed 64 cuts40618 = true := by
 decide +kernel
def pointBounds40618 : List (Nat × Nat × Nat) := [(5327890432,109059014804564,109059400424549)]
theorem point_links_checked40618 : (cuts40618.take 1).map (fun c => (5327814657-1+2*2^10*c.k,109058837134477+c.lower,109059222754356+c.upper)) = pointBounds40618 := by
 decide +kernel
def cuts40619 : List PrefixCut := [⟨55,265995766,265995925⟩,
⟨64,309526616,309526800⟩]
theorem checked40619 : checkPrefixCuts (2^48) 5327945729 10 Manual.Count131072.C040619.packed 64 cuts40619 = true := by
 decide +kernel
def pointBounds40619 : List (Nat × Nat × Nat) := [(5328058368,109059412981445,109059798601669)]
theorem point_links_checked40619 : (cuts40619.take 1).map (fun c => (5327945729-1+2*2^10*c.k,109059146985679+c.lower,109059532605744+c.upper)) = pointBounds40619 := by
 decide +kernel
def cuts40620 : List PrefixCut := [⟨64,309413410,309413597⟩]
theorem checked40620 : checkPrefixCuts (2^48) 5328076801 10 Manual.Count131072.C040620.packed 64 cuts40620 = true := by
 decide +kernel
def cuts40621 : List PrefixCut := [⟨9,43476803,43476829⟩,
⟨64,312892305,312892490⟩]
theorem checked40621 : checkPrefixCuts (2^48) 5328207873 10 Manual.Count131072.C040621.packed 64 cuts40621 = true := by
 decide +kernel
def pointBounds40621 : List (Nat × Nat × Nat) := [(5328226304,109059809402508,109060195022970)]
theorem point_links_checked40621 : (cuts40621.take 1).map (fun c => (5328207873-1+2*2^10*c.k,109059765925705+c.lower,109060151546141+c.upper)) = pointBounds40621 := by
 decide +kernel
def cuts40622 : List PrefixCut := [⟨27,130796526,130796603⟩,
⟨64,311405491,311405675⟩]
theorem checked40622 : checkPrefixCuts (2^48) 5328338945 10 Manual.Count131072.C040622.packed 64 cuts40622 = true := by
 decide +kernel
def pointBounds40622 : List (Nat × Nat × Nat) := [(5328394240,109060209614536,109060595235234)]
theorem point_links_checked40622 : (cuts40622.take 1).map (fun c => (5328338945-1+2*2^10*c.k,109060078818010+c.lower,109060464438631+c.upper)) = pointBounds40622 := by
 decide +kernel
def cuts40623 : List PrefixCut := [⟨45,217952861,217952990⟩,
⟨64,307541697,307541879⟩]
theorem checked40623 : checkPrefixCuts (2^48) 5328470017 10 Manual.Count131072.C040623.packed 64 cuts40623 = true := by
 decide +kernel
def pointBounds40623 : List (Nat × Nat × Nat) := [(5328562176,109060608176362,109060993797296)]
theorem point_links_checked40623 : (cuts40623.take 1).map (fun c => (5328470017-1+2*2^10*c.k,109060390223501+c.lower,109060775844306+c.upper)) = pointBounds40623 := by
 decide +kernel
def cuts40624 : List PrefixCut := [⟨63,300455931,300456109⟩,
⟨64,305632499,305632680⟩]
theorem checked40624 : checkPrefixCuts (2^48) 5328601089 10 Manual.Count131072.C040624.packed 64 cuts40624 = true := by
 decide +kernel
def pointBounds40624 : List (Nat × Nat × Nat) := [(5328730112,109060998221129,109061383842294)]
theorem point_links_checked40624 : (cuts40624.take 1).map (fun c => (5328601089-1+2*2^10*c.k,109060697765198+c.lower,109061083386185+c.upper)) = pointBounds40624 := by
 decide +kernel
def cuts40625 : List PrefixCut := [⟨64,311752279,311752463⟩]
theorem checked40625 : checkPrefixCuts (2^48) 5328732161 10 Manual.Count131072.C040625.packed 64 cuts40625 = true := by
 decide +kernel
def cuts40626 : List PrefixCut := [⟨17,82453019,82453068⟩,
⟨64,311163596,311163781⟩]
theorem checked40626 : checkPrefixCuts (2^48) 5328863233 10 Manual.Count131072.C040626.packed 64 cuts40626 = true := by
 decide +kernel
def pointBounds40626 : List (Nat × Nat × Nat) := [(5328898048,109061397602995,109061783224396)]
theorem point_links_checked40626 : (cuts40626.take 1).map (fun c => (5328863233-1+2*2^10*c.k,109061315149976+c.lower,109061700771328+c.upper)) = pointBounds40626 := by
 decide +kernel
def cuts40627 : List PrefixCut := [⟨35,167859304,167859401⟩,
⟨64,310416469,310416646⟩]
theorem checked40627 : checkPrefixCuts (2^48) 5328994305 10 Manual.Count131072.C040627.packed 64 cuts40627 = true := by
 decide +kernel
def pointBounds40627 : List (Nat × Nat × Nat) := [(5329065984,109061794172876,109062179794510)]
theorem point_links_checked40627 : (cuts40627.take 1).map (fun c => (5328994305-1+2*2^10*c.k,109061626313572+c.lower,109062011935109+c.upper)) = pointBounds40627 := by
 decide +kernel
def cuts40628 : List PrefixCut := [⟨53,255637570,255637719⟩,
⟨64,307503892,307504073⟩]
theorem checked40628 : checkPrefixCuts (2^48) 5329125377 10 Manual.Count131072.C040628.packed 64 cuts40628 = true := by
 decide +kernel
def pointBounds40628 : List (Nat × Nat × Nat) := [(5329233920,109062192367611,109062577989474)]
theorem point_links_checked40628 : (cuts40628.take 1).map (fun c => (5329125377-1+2*2^10*c.k,109061936730041+c.lower,109062322351755+c.upper)) = pointBounds40628 := by
 decide +kernel
def cuts40629 : List PrefixCut := [⟨64,307020957,307021138⟩]
theorem checked40629 : checkPrefixCuts (2^48) 5329256449 10 Manual.Count131072.C040629.packed 64 cuts40629 = true := by
 decide +kernel
def cuts40630 : List PrefixCut := [⟨7,34382922,34382943⟩,
⟨64,310076685,310076868⟩]
theorem checked40630 : checkPrefixCuts (2^48) 5329387521 10 Manual.Count131072.C040630.packed 64 cuts40630 = true := by
 decide +kernel
def pointBounds40630 : List (Nat × Nat × Nat) := [(5329401856,109062585637812,109062971259909)]
theorem point_links_checked40630 : (cuts40630.take 1).map (fun c => (5329387521-1+2*2^10*c.k,109062551254890+c.lower,109062936876966+c.upper)) = pointBounds40630 := by
 decide +kernel
def cuts40631 : List PrefixCut := [⟨25,119306974,119307046⟩,
⟨64,303520161,303520341⟩]
theorem checked40631 : checkPrefixCuts (2^48) 5329518593 10 Manual.Count131072.C040631.packed 64 cuts40631 = true := by
 decide +kernel
def pointBounds40631 : List (Nat × Nat × Nat) := [(5329569792,109062980638549,109063366260880)]
theorem point_links_checked40631 : (cuts40631.take 1).map (fun c => (5329518593-1+2*2^10*c.k,109062861331575+c.lower,109063246953834+c.upper)) = pointBounds40631 := by
 decide +kernel
def cuts40632 : List PrefixCut := [⟨43,209507518,209507642⟩,
⟨64,310800807,310800993⟩]
theorem checked40632 : checkPrefixCuts (2^48) 5329649665 10 Manual.Count131072.C040632.packed 64 cuts40632 = true := by
 decide +kernel
def pointBounds40632 : List (Nat × Nat × Nat) := [(5329737728,109063374359254,109063759981817)]
theorem point_links_checked40632 : (cuts40632.take 1).map (fun c => (5329649665-1+2*2^10*c.k,109063164851736+c.lower,109063550474175+c.upper)) = pointBounds40632 := by
 decide +kernel
def cuts40633 : List PrefixCut := [⟨61,297168077,297168252⟩,
⟨64,310898795,310898978⟩]
theorem checked40633 : checkPrefixCuts (2^48) 5329780737 10 Manual.Count131072.C040633.packed 64 cuts40633 = true := by
 decide +kernel
def pointBounds40633 : List (Nat × Nat × Nat) := [(5329905664,109063772820620,109064158443420)]
theorem point_links_checked40633 : (cuts40633.take 1).map (fun c => (5329780737-1+2*2^10*c.k,109063475652543+c.lower,109063861275168+c.upper)) = pointBounds40633 := by
 decide +kernel
def cuts40634 : List PrefixCut := [⟨64,308778750,308778931⟩]
theorem checked40634 : checkPrefixCuts (2^48) 5329911809 10 Manual.Count131072.C040634.packed 64 cuts40634 = true := by
 decide +kernel
def cuts40635 : List PrefixCut := [⟨15,71133685,71133727⟩,
⟨64,308295879,308296062⟩]
theorem checked40635 : checkPrefixCuts (2^48) 5330042881 10 Manual.Count131072.C040635.packed 64 cuts40635 = true := by
 decide +kernel
def pointBounds40635 : List (Nat × Nat × Nat) := [(5330073600,109064166463773,109064552086804)]
theorem point_links_checked40635 : (cuts40635.take 1).map (fun c => (5330042881-1+2*2^10*c.k,109064095330088+c.lower,109064480953077+c.upper)) = pointBounds40635 := by
 decide +kernel
def cuts40636 : List PrefixCut := [⟨33,159689846,159689940⟩,
⟨64,307232162,307232345⟩]
theorem checked40636 : checkPrefixCuts (2^48) 5330173953 10 Manual.Count131072.C040636.packed 64 cuts40636 = true := by
 decide +kernel
def pointBounds40636 : List (Nat × Nat × Nat) := [(5330241536,109064563315813,109064948939079)]
theorem point_links_checked40636 : (cuts40636.take 1).map (fun c => (5330173953-1+2*2^10*c.k,109064403625967+c.lower,109064789249139+c.upper)) = pointBounds40636 := by
 decide +kernel
def cuts40637 : List PrefixCut := [⟨51,248874721,248874867⟩,
⟨64,312769207,312769391⟩]
theorem checked40637 : checkPrefixCuts (2^48) 5330305025 10 Manual.Count131072.C040637.packed 64 cuts40637 = true := by
 decide +kernel
def pointBounds40637 : List (Nat × Nat × Nat) := [(5330409472,109064959732850,109065345356351)]
theorem point_links_checked40637 : (cuts40637.take 1).map (fun c => (5330305025-1+2*2^10*c.k,109064710858129+c.lower,109065096481484+c.upper)) = pointBounds40637 := by
 decide +kernel
def cuts40638 : List PrefixCut := [⟨64,306372160,306372340⟩]
theorem checked40638 : checkPrefixCuts (2^48) 5330436097 10 Manual.Count131072.C040638.packed 64 cuts40638 = true := by
 decide +kernel
def cuts40639 : List PrefixCut := [⟨5,24078570,24078585⟩,
⟨64,307684716,307684894⟩]
theorem checked40639 : checkPrefixCuts (2^48) 5330567169 10 Manual.Count131072.C040639.packed 64 cuts40639 = true := by
 decide +kernel
def pointBounds40639 : List (Nat × Nat × Nat) := [(5330577408,109065354078066,109065739701800)]
theorem point_links_checked40639 : (cuts40639.take 1).map (fun c => (5330567169-1+2*2^10*c.k,109065329999496+c.lower,109065715623215+c.upper)) = pointBounds40639 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000019
