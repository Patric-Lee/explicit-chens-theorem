import PlattAssemblyKernel
import PlattCertificates.Count131072.C051600
import PlattCertificates.Count131072.C051601
import PlattCertificates.Count131072.C051602
import PlattCertificates.Count131072.C051603
import PlattCertificates.Count131072.C051604
import PlattCertificates.Count131072.C051605
import PlattCertificates.Count131072.C051606
import PlattCertificates.Count131072.C051607
import PlattCertificates.Count131072.C051608
import PlattCertificates.Count131072.C051609
import PlattCertificates.Count131072.C051610
import PlattCertificates.Count131072.C051611
import PlattCertificates.Count131072.C051612
import PlattCertificates.Count131072.C051613
import PlattCertificates.Count131072.C051614
import PlattCertificates.Count131072.C051615
import PlattCertificates.Count131072.C051616
import PlattCertificates.Count131072.C051617
import PlattCertificates.Count131072.C051618
import PlattCertificates.Count131072.C051619
import PlattCertificates.Count131072.C051620
import PlattCertificates.Count131072.C051621
import PlattCertificates.Count131072.C051622
import PlattCertificates.Count131072.C051623
import PlattCertificates.Count131072.C051624
import PlattCertificates.Count131072.C051625
import PlattCertificates.Count131072.C051626
import PlattCertificates.Count131072.C051627
import PlattCertificates.Count131072.C051628
import PlattCertificates.Count131072.C051629
import PlattCertificates.Count131072.C051630
import PlattCertificates.Count131072.C051631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51600 : List PrefixCut := [⟨64,237123404,237123539⟩]
theorem checked51600 : checkPrefixCuts (2^48) 6767247361 10 Manual.Count131072.C051600.packed 64 cuts51600 = true := by
 decide +kernel
def cuts51601 : List PrefixCut := [⟨27,100696005,100696061⟩,
⟨64,241444443,241444577⟩]
theorem checked51601 : checkPrefixCuts (2^48) 6767378433 10 Manual.Count131072.C051601.packed 64 cuts51601 = true := by
 decide +kernel
def pointBounds51601 : List (Nat × Nat × Nat) := [(6767433728,112048941993321,112049329338317)]
theorem point_links_checked51601 : (cuts51601.take 1).map (fun c => (6767378433-1+2*2^10*c.k,112048841297316+c.lower,112049228642256+c.upper)) = pointBounds51601 := by
 decide +kernel
def cuts51602 : List PrefixCut := [⟨64,241315000,241315135⟩]
theorem checked51602 : checkPrefixCuts (2^48) 6767509505 10 Manual.Count131072.C051602.packed 64 cuts51602 = true := by
 decide +kernel
def cuts51603 : List PrefixCut := [⟨3,11271234,11271241⟩,
⟨64,240644866,240645006⟩]
theorem checked51603 : checkPrefixCuts (2^48) 6767640577 10 Manual.Count131072.C051603.packed 64 cuts51603 = true := by
 decide +kernel
def pointBounds51603 : List (Nat × Nat × Nat) := [(6767646720,112049335327993,112049722673209)]
theorem point_links_checked51603 : (cuts51603.take 1).map (fun c => (6767640577-1+2*2^10*c.k,112049324056759+c.lower,112049711401968+c.upper)) = pointBounds51603 := by
 decide +kernel
def cuts51604 : List PrefixCut := [⟨43,164239748,164239839⟩,
⟨64,244591256,244591393⟩]
theorem checked51604 : checkPrefixCuts (2^48) 6767771649 10 Manual.Count131072.C051604.packed 64 cuts51604 = true := by
 decide +kernel
def pointBounds51604 : List (Nat × Nat × Nat) := [(6767859712,112049728941373,112050116286813)]
theorem point_links_checked51604 : (cuts51604.take 1).map (fun c => (6767771649-1+2*2^10*c.k,112049564701625+c.lower,112049952046974+c.upper)) = pointBounds51604 := by
 decide +kernel
def cuts51605 : List PrefixCut := [⟨64,239263105,239263241⟩]
theorem checked51605 : checkPrefixCuts (2^48) 6767902721 10 Manual.Count131072.C051605.packed 64 cuts51605 = true := by
 decide +kernel
def cuts51606 : List PrefixCut := [⟨19,70700883,70700923⟩,
⟨64,239300066,239300204⟩]
theorem checked51606 : checkPrefixCuts (2^48) 6768033793 10 Manual.Count131072.C051606.packed 64 cuts51606 = true := by
 decide +kernel
def pointBounds51606 : List (Nat × Nat × Nat) := [(6768072704,112050119256869,112050506602531)]
theorem point_links_checked51606 : (cuts51606.take 1).map (fun c => (6768033793-1+2*2^10*c.k,112050048555986+c.lower,112050435901608+c.upper)) = pointBounds51606 := by
 decide +kernel
def cuts51607 : List PrefixCut := [⟨59,221745590,221745718⟩,
⟨64,240043999,240044138⟩]
theorem checked51607 : checkPrefixCuts (2^48) 6768164865 10 Manual.Count131072.C051607.packed 64 cuts51607 = true := by
 decide +kernel
def pointBounds51607 : List (Nat × Nat × Nat) := [(6768285696,112050509601642,112050896947530)]
theorem point_links_checked51607 : (cuts51607.take 1).map (fun c => (6768164865-1+2*2^10*c.k,112050287856052+c.lower,112050675201812+c.upper)) = pointBounds51607 := by
 decide +kernel
def cuts51608 : List PrefixCut := [⟨64,242617739,242617878⟩]
theorem checked51608 : checkPrefixCuts (2^48) 6768295937 10 Manual.Count131072.C051608.packed 64 cuts51608 = true := by
 decide +kernel
def cuts51609 : List PrefixCut := [⟨35,133200723,133200801⟩,
⟨64,245565653,245565793⟩]
theorem checked51609 : checkPrefixCuts (2^48) 6768427009 10 Manual.Count131072.C051609.packed 64 cuts51609 = true := by
 decide +kernel
def pointBounds51609 : List (Nat × Nat × Nat) := [(6768498688,112050903718513,112051291064629)]
theorem point_links_checked51609 : (cuts51609.take 1).map (fun c => (6768427009-1+2*2^10*c.k,112050770517790+c.lower,112051157863828+c.upper)) = pointBounds51609 := by
 decide +kernel
def cuts51610 : List PrefixCut := [⟨64,239364703,239364843⟩]
theorem checked51610 : checkPrefixCuts (2^48) 6768558081 10 Manual.Count131072.C051610.packed 64 cuts51610 = true := by
 decide +kernel
def cuts51611 : List PrefixCut := [⟨11,43747187,43747211⟩,
⟨64,244807642,244807786⟩]
theorem checked51611 : checkPrefixCuts (2^48) 6768689153 10 Manual.Count131072.C051611.packed 64 cuts51611 = true := by
 decide +kernel
def pointBounds51611 : List (Nat × Nat × Nat) := [(6768711680,112051299195333,112051686541675)]
theorem point_links_checked51611 : (cuts51611.take 1).map (fun c => (6768689153-1+2*2^10*c.k,112051255448146+c.lower,112051642794464+c.upper)) = pointBounds51611 := by
 decide +kernel
def cuts51612 : List PrefixCut := [⟨51,190994036,190994144⟩,
⟨64,239397018,239397154⟩]
theorem checked51612 : checkPrefixCuts (2^48) 6768820225 10 Manual.Count131072.C051612.packed 64 cuts51612 = true := by
 decide +kernel
def pointBounds51612 : List (Nat × Nat × Nat) := [(6768924672,112051691249824,112052078596394)]
theorem point_links_checked51612 : (cuts51612.take 1).map (fun c => (6768820225-1+2*2^10*c.k,112051500255788+c.lower,112051887602250+c.upper)) = pointBounds51612 := by
 decide +kernel
def cuts51613 : List PrefixCut := [⟨64,239018109,239018251⟩]
theorem checked51613 : checkPrefixCuts (2^48) 6768951297 10 Manual.Count131072.C051613.packed 64 cuts51613 = true := by
 decide +kernel
def cuts51614 : List PrefixCut := [⟨27,99963762,99963819⟩,
⟨64,240302527,240302663⟩]
theorem checked51614 : checkPrefixCuts (2^48) 6769082369 10 Manual.Count131072.C051614.packed 64 cuts51614 = true := by
 decide +kernel
def pointBounds51614 : List (Nat × Nat × Nat) := [(6769137664,112052078634677,112052465981474)]
theorem point_links_checked51614 : (cuts51614.take 1).map (fun c => (6769082369-1+2*2^10*c.k,112051978670915+c.lower,112052366017655+c.upper)) = pointBounds51614 := by
 decide +kernel
def cuts51615 : List PrefixCut := [⟨64,241337423,241337559⟩]
theorem checked51615 : checkPrefixCuts (2^48) 6769213441 10 Manual.Count131072.C051615.packed 64 cuts51615 = true := by
 decide +kernel
def cuts51616 : List PrefixCut := [⟨3,10478362,10478368⟩,
⟨64,241790114,241790251⟩]
theorem checked51616 : checkPrefixCuts (2^48) 6769344513 10 Manual.Count131072.C051616.packed 64 cuts51616 = true := by
 decide +kernel
def pointBounds51616 : List (Nat × Nat × Nat) := [(6769350656,112052470789227,112052858136245)]
theorem point_links_checked51616 : (cuts51616.take 1).map (fun c => (6769344513-1+2*2^10*c.k,112052460310865+c.lower,112052847657877+c.upper)) = pointBounds51616 := by
 decide +kernel
def cuts51617 : List PrefixCut := [⟨43,162826288,162826380⟩,
⟨64,242908100,242908236⟩]
theorem checked51617 : checkPrefixCuts (2^48) 6769475585 10 Manual.Count131072.C051617.packed 64 cuts51617 = true := by
 decide +kernel
def pointBounds51617 : List (Nat × Nat × Nat) := [(6769563648,112052864927267,112053252274508)]
theorem point_links_checked51617 : (cuts51617.take 1).map (fun c => (6769475585-1+2*2^10*c.k,112052702100979+c.lower,112053089448128+c.upper)) = pointBounds51617 := by
 decide +kernel
def cuts51618 : List PrefixCut := [⟨64,240325508,240325646⟩]
theorem checked51618 : checkPrefixCuts (2^48) 6769606657 10 Manual.Count131072.C051618.packed 64 cuts51618 = true := by
 decide +kernel
def cuts51619 : List PrefixCut := [⟨19,71805699,71805738⟩,
⟨64,240611910,240612052⟩]
theorem checked51619 : checkPrefixCuts (2^48) 6769737729 10 Manual.Count131072.C051619.packed 64 cuts51619 = true := by
 decide +kernel
def pointBounds51619 : List (Nat × Nat × Nat) := [(6769776640,112053257140286,112053644487748)]
theorem point_links_checked51619 : (cuts51619.take 1).map (fun c => (6769737729-1+2*2^10*c.k,112053185334587+c.lower,112053572682010+c.upper)) = pointBounds51619 := by
 decide +kernel
def cuts51620 : List PrefixCut := [⟨59,220151437,220151566⟩,
⟨64,238944163,238944302⟩]
theorem checked51620 : checkPrefixCuts (2^48) 6769868801 10 Manual.Count131072.C051620.packed 64 cuts51620 = true := by
 decide +kernel
def pointBounds51620 : List (Nat × Nat × Nat) := [(6769989632,112053646097934,112054033445628)]
theorem point_links_checked51620 : (cuts51620.take 1).map (fun c => (6769868801-1+2*2^10*c.k,112053425946497+c.lower,112053813294062+c.upper)) = pointBounds51620 := by
 decide +kernel
def cuts51621 : List PrefixCut := [⟨64,245882793,245882931⟩]
theorem checked51621 : checkPrefixCuts (2^48) 6769999873 10 Manual.Count131072.C051621.packed 64 cuts51621 = true := by
 decide +kernel
def cuts51622 : List PrefixCut := [⟨35,132543564,132543635⟩,
⟨64,243050898,243051031⟩]
theorem checked51622 : checkPrefixCuts (2^48) 6770130945 10 Manual.Count131072.C051622.packed 64 cuts51622 = true := by
 decide +kernel
def pointBounds51622 : List (Nat × Nat × Nat) := [(6770202624,112054043317017,112054430664930)]
theorem point_links_checked51622 : (cuts51622.take 1).map (fun c => (6770130945-1+2*2^10*c.k,112053910773453+c.lower,112054298121295+c.upper)) = pointBounds51622 := by
 decide +kernel
def cuts51623 : List PrefixCut := [⟨64,240094389,240094527⟩]
theorem checked51623 : checkPrefixCuts (2^48) 6770262017 10 Manual.Count131072.C051623.packed 64 cuts51623 = true := by
 decide +kernel
def cuts51624 : List PrefixCut := [⟨11,41990053,41990077⟩,
⟨64,239341387,239341522⟩]
theorem checked51624 : checkPrefixCuts (2^48) 6770393089 10 Manual.Count131072.C051624.packed 64 cuts51624 = true := by
 decide +kernel
def pointBounds51624 : List (Nat × Nat × Nat) := [(6770415616,112054435908793,112054823256930)]
theorem point_links_checked51624 : (cuts51624.take 1).map (fun c => (6770393089-1+2*2^10*c.k,112054393918740+c.lower,112054781266853+c.upper)) = pointBounds51624 := by
 decide +kernel
def cuts51625 : List PrefixCut := [⟨51,192110022,192110129⟩,
⟨64,241290708,241290843⟩]
theorem checked51625 : checkPrefixCuts (2^48) 6770524161 10 Manual.Count131072.C051625.packed 64 cuts51625 = true := by
 decide +kernel
def pointBounds51625 : List (Nat × Nat × Nat) := [(6770628608,112054825370149,112055212718504)]
theorem point_links_checked51625 : (cuts51625.take 1).map (fun c => (6770524161-1+2*2^10*c.k,112054633260127+c.lower,112055020608375+c.upper)) = pointBounds51625 := by
 decide +kernel
def cuts51626 : List PrefixCut := [⟨64,239248982,239249118⟩]
theorem checked51626 : checkPrefixCuts (2^48) 6770655233 10 Manual.Count131072.C051626.packed 64 cuts51626 = true := by
 decide +kernel
def cuts51627 : List PrefixCut := [⟨27,100770034,100770092⟩,
⟨64,240616201,240616340⟩]
theorem checked51627 : checkPrefixCuts (2^48) 6770786305 10 Manual.Count131072.C051627.packed 64 cuts51627 = true := by
 decide +kernel
def pointBounds51627 : List (Nat × Nat × Nat) := [(6770841600,112055214569851,112055601918428)]
theorem point_links_checked51627 : (cuts51627.take 1).map (fun c => (6770786305-1+2*2^10*c.k,112055113799817+c.lower,112055501148336+c.upper)) = pointBounds51627 := by
 decide +kernel
def cuts51628 : List PrefixCut := [⟨64,243272082,243272223⟩]
theorem checked51628 : checkPrefixCuts (2^48) 6770917377 10 Manual.Count131072.C051628.packed 64 cuts51628 = true := by
 decide +kernel
def cuts51629 : List PrefixCut := [⟨3,11473413,11473420⟩,
⟨64,241188886,241189029⟩]
theorem checked51629 : checkPrefixCuts (2^48) 6771048449 10 Manual.Count131072.C051629.packed 64 cuts51629 = true := by
 decide +kernel
def pointBounds51629 : List (Nat × Nat × Nat) := [(6771054592,112055609161513,112055996510319)]
theorem point_links_checked51629 : (cuts51629.take 1).map (fun c => (6771048449-1+2*2^10*c.k,112055597688100+c.lower,112055985036899+c.upper)) = pointBounds51629 := by
 decide +kernel
def cuts51630 : List PrefixCut := [⟨43,160914694,160914785⟩,
⟨64,239770856,239770992⟩]
theorem checked51630 : checkPrefixCuts (2^48) 6771179521 10 Manual.Count131072.C051630.packed 64 cuts51630 = true := by
 decide +kernel
def pointBounds51630 : List (Nat × Nat × Nat) := [(6771267584,112055999791680,112056387140713)]
theorem point_links_checked51630 : (cuts51630.take 1).map (fun c => (6771179521-1+2*2^10*c.k,112055838876986+c.lower,112056226225928+c.upper)) = pointBounds51630 := by
 decide +kernel
def cuts51631 : List PrefixCut := [⟨64,239142673,239142811⟩]
theorem checked51631 : checkPrefixCuts (2^48) 6771310593 10 Manual.Count131072.C051631.packed 64 cuts51631 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000050
