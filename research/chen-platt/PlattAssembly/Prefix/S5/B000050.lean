import PlattAssemblyKernel
import PlattCertificates.Count131072.C041600
import PlattCertificates.Count131072.C041601
import PlattCertificates.Count131072.C041602
import PlattCertificates.Count131072.C041603
import PlattCertificates.Count131072.C041604
import PlattCertificates.Count131072.C041605
import PlattCertificates.Count131072.C041606
import PlattCertificates.Count131072.C041607
import PlattCertificates.Count131072.C041608
import PlattCertificates.Count131072.C041609
import PlattCertificates.Count131072.C041610
import PlattCertificates.Count131072.C041611
import PlattCertificates.Count131072.C041612
import PlattCertificates.Count131072.C041613
import PlattCertificates.Count131072.C041614
import PlattCertificates.Count131072.C041615
import PlattCertificates.Count131072.C041616
import PlattCertificates.Count131072.C041617
import PlattCertificates.Count131072.C041618
import PlattCertificates.Count131072.C041619
import PlattCertificates.Count131072.C041620
import PlattCertificates.Count131072.C041621
import PlattCertificates.Count131072.C041622
import PlattCertificates.Count131072.C041623
import PlattCertificates.Count131072.C041624
import PlattCertificates.Count131072.C041625
import PlattCertificates.Count131072.C041626
import PlattCertificates.Count131072.C041627
import PlattCertificates.Count131072.C041628
import PlattCertificates.Count131072.C041629
import PlattCertificates.Count131072.C041630
import PlattCertificates.Count131072.C041631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41600 : List PrefixCut := [⟨9,41113166,41113191⟩,
⟨64,302284376,302284553⟩]
theorem checked41600 : checkPrefixCuts (2^48) 5456527361 10 Manual.Count131072.C041600.packed 64 cuts41600 = true := by
 decide +kernel
def pointBounds41600 : List (Nat × Nat × Nat) := [(5456545792,109358706305072,109359092101760)]
theorem point_links_checked41600 : (cuts41600.take 1).map (fun c => (5456527361-1+2*2^10*c.k,109358665191906+c.lower,109359050988569+c.upper)) = pointBounds41600 := by
 decide +kernel
def cuts41601 : List PrefixCut := [⟨29,137882605,137882687⟩,
⟨64,302586638,302586815⟩]
theorem checked41601 : checkPrefixCuts (2^48) 5456658433 10 Manual.Count131072.C041601.packed 64 cuts41601 = true := by
 decide +kernel
def pointBounds41601 : List (Nat × Nat × Nat) := [(5456717824,109359105358887,109359491155809)]
theorem point_links_checked41601 : (cuts41601.take 1).map (fun c => (5456658433-1+2*2^10*c.k,109358967476282+c.lower,109359353273122+c.upper)) = pointBounds41601 := by
 decide +kernel
def cuts41602 : List PrefixCut := [⟨49,231500180,231500318⟩,
⟨64,301496162,301496340⟩]
theorem checked41602 : checkPrefixCuts (2^48) 5456789505 10 Manual.Count131072.C041602.packed 64 cuts41602 = true := by
 decide +kernel
def pointBounds41602 : List (Nat × Nat × Nat) := [(5456889856,109359501563100,109359887360255)]
theorem point_links_checked41602 : (cuts41602.take 1).map (fun c => (5456789505-1+2*2^10*c.k,109359270062920+c.lower,109359655859937+c.upper)) = pointBounds41602 := by
 decide +kernel
def cuts41603 : List PrefixCut := [⟨64,303345796,303345970⟩]
theorem checked41603 : checkPrefixCuts (2^48) 5456920577 10 Manual.Count131072.C041603.packed 64 cuts41603 = true := by
 decide +kernel
def cuts41604 : List PrefixCut := [⟨5,22695192,22695205⟩,
⟨64,300140586,300140765⟩]
theorem checked41604 : checkPrefixCuts (2^48) 5457051649 10 Manual.Count131072.C041604.packed 64 cuts41604 = true := by
 decide +kernel
def pointBounds41604 : List (Nat × Nat × Nat) := [(5457061888,109359897600070,109360283397452)]
theorem point_links_checked41604 : (cuts41604.take 1).map (fun c => (5457051649-1+2*2^10*c.k,109359874904878+c.lower,109360260702247+c.upper)) = pointBounds41604 := by
 decide +kernel
def cuts41605 : List PrefixCut := [⟨25,120178014,120178087⟩,
⟨64,303692291,303692469⟩]
theorem checked41605 : checkPrefixCuts (2^48) 5457182721 10 Manual.Count131072.C041605.packed 64 cuts41605 = true := by
 decide +kernel
def pointBounds41605 : List (Nat × Nat × Nat) := [(5457233920,109360295223478,109360681021099)]
theorem point_links_checked41605 : (cuts41605.take 1).map (fun c => (5457182721-1+2*2^10*c.k,109360175045464+c.lower,109360560843012+c.upper)) = pointBounds41605 := by
 decide +kernel
def cuts41606 : List PrefixCut := [⟨45,207082117,207082236⟩,
⟨64,296154727,296154899⟩]
theorem checked41606 : checkPrefixCuts (2^48) 5457313793 10 Manual.Count131072.C041606.packed 64 cuts41606 = true := by
 decide +kernel
def pointBounds41606 : List (Nat × Nat × Nat) := [(5457405952,109360685819872,109361071617717)]
theorem point_links_checked41606 : (cuts41606.take 1).map (fun c => (5457313793-1+2*2^10*c.k,109360478737755+c.lower,109360864535481+c.upper)) = pointBounds41606 := by
 decide +kernel
def cuts41607 : List PrefixCut := [⟨64,307803730,307803905⟩]
theorem checked41607 : checkPrefixCuts (2^48) 5457444865 10 Manual.Count131072.C041607.packed 64 cuts41607 = true := by
 decide +kernel
def cuts41608 : List PrefixCut := [⟨1,4590181,4590184⟩,
⟨64,304547179,304547356⟩]
theorem checked41608 : checkPrefixCuts (2^48) 5457575937 10 Manual.Count131072.C041608.packed 64 cuts41608 = true := by
 decide +kernel
def pointBounds41608 : List (Nat × Nat × Nat) := [(5457577984,109361087286393,109361473084469)]
theorem point_links_checked41608 : (cuts41608.take 1).map (fun c => (5457575937-1+2*2^10*c.k,109361082696212+c.lower,109361468494285+c.upper)) = pointBounds41608 := by
 decide +kernel
def cuts41609 : List PrefixCut := [⟨21,99176093,99176152⟩,
⟨64,302115891,302116067⟩]
theorem checked41609 : checkPrefixCuts (2^48) 5457707009 10 Manual.Count131072.C041609.packed 64 cuts41609 = true := by
 decide +kernel
def pointBounds41609 : List (Nat × Nat × Nat) := [(5457750016,109361486419484,109361872217793)]
theorem point_links_checked41609 : (cuts41609.take 1).map (fun c => (5457707009-1+2*2^10*c.k,109361387243391+c.lower,109361773041641+c.upper)) = pointBounds41609 := by
 decide +kernel
def cuts41610 : List PrefixCut := [⟨41,191745438,191745554⟩,
⟨64,296693604,296693781⟩]
theorem checked41610 : checkPrefixCuts (2^48) 5457838081 10 Manual.Count131072.C041610.packed 64 cuts41610 = true := by
 decide +kernel
def pointBounds41610 : List (Nat × Nat × Nat) := [(5457922048,109361881104720,109362266903262)]
theorem point_links_checked41610 : (cuts41610.take 1).map (fun c => (5457838081-1+2*2^10*c.k,109361689359282+c.lower,109362075157708+c.upper)) = pointBounds41610 := by
 decide +kernel
def cuts41611 : List PrefixCut := [⟨61,288951046,288951221⟩,
⟨64,303648539,303648723⟩]
theorem checked41611 : checkPrefixCuts (2^48) 5457969153 10 Manual.Count131072.C041611.packed 64 cuts41611 = true := by
 decide +kernel
def pointBounds41611 : List (Nat × Nat × Nat) := [(5458094080,109362275003932,109362660802710)]
theorem point_links_checked41611 : (cuts41611.take 1).map (fun c => (5457969153-1+2*2^10*c.k,109361986052886+c.lower,109362371851489+c.upper)) = pointBounds41611 := by
 decide +kernel
def cuts41612 : List PrefixCut := [⟨64,299464115,299464285⟩]
theorem checked41612 : checkPrefixCuts (2^48) 5458100225 10 Manual.Count131072.C041612.packed 64 cuts41612 = true := by
 decide +kernel
def cuts41613 : List PrefixCut := [⟨17,79879945,79879990⟩,
⟨64,302086894,302087071⟩]
theorem checked41613 : checkPrefixCuts (2^48) 5458231297 10 Manual.Count131072.C041613.packed 64 cuts41613 = true := by
 decide +kernel
def pointBounds41613 : List (Nat × Nat × Nat) := [(5458266112,109362669045485,109363054844487)]
theorem point_links_checked41613 : (cuts41613.take 1).map (fun c => (5458231297-1+2*2^10*c.k,109362589165540+c.lower,109362974964497+c.upper)) = pointBounds41613 := by
 decide +kernel
def cuts41614 : List PrefixCut := [⟨37,175483474,175483579⟩,
⟨64,303110975,303111153⟩]
theorem checked41614 : checkPrefixCuts (2^48) 5458362369 10 Manual.Count131072.C041614.packed 64 cuts41614 = true := by
 decide +kernel
def pointBounds41614 : List (Nat × Nat × Nat) := [(5458438144,109363066735908,109363452535147)]
theorem point_links_checked41614 : (cuts41614.take 1).map (fun c => (5458362369-1+2*2^10*c.k,109362891252434+c.lower,109363277051568+c.upper)) = pointBounds41614 := by
 decide +kernel
def cuts41615 : List PrefixCut := [⟨57,269998828,269998987⟩,
⟨64,302897449,302897627⟩]
theorem checked41615 : checkPrefixCuts (2^48) 5458493441 10 Manual.Count131072.C041615.packed 64 cuts41615 = true := by
 decide +kernel
def pointBounds41615 : List (Nat × Nat × Nat) := [(5458610176,109363464362237,109363850161708)]
theorem point_links_checked41615 : (cuts41615.take 1).map (fun c => (5458493441-1+2*2^10*c.k,109363194363409+c.lower,109363580162721+c.upper)) = pointBounds41615 := by
 decide +kernel
def cuts41616 : List PrefixCut := [⟨64,304694934,304695111⟩]
theorem checked41616 : checkPrefixCuts (2^48) 5458624513 10 Manual.Count131072.C041616.packed 64 cuts41616 = true := by
 decide +kernel
def cuts41617 : List PrefixCut := [⟨13,63268788,63268824⟩,
⟨64,301593807,301593982⟩]
theorem checked41617 : checkPrefixCuts (2^48) 5458755585 10 Manual.Count131072.C041617.packed 64 cuts41617 = true := by
 decide +kernel
def pointBounds41617 : List (Nat × Nat × Nat) := [(5458782208,109363865224580,109364251024283)]
theorem point_links_checked41617 : (cuts41617.take 1).map (fun c => (5458755585-1+2*2^10*c.k,109363801955792+c.lower,109364187755459+c.upper)) = pointBounds41617 := by
 decide +kernel
def cuts41618 : List PrefixCut := [⟨33,153243377,153243466⟩,
⟨64,299575644,299575820⟩]
theorem checked41618 : checkPrefixCuts (2^48) 5458886657 10 Manual.Count131072.C041618.packed 64 cuts41618 = true := by
 decide +kernel
def pointBounds41618 : List (Nat × Nat × Nat) := [(5458954240,109364256792976,109364642592907)]
theorem point_links_checked41618 : (cuts41618.take 1).map (fun c => (5458886657-1+2*2^10*c.k,109364103549599+c.lower,109364489349441+c.upper)) = pointBounds41618 := by
 decide +kernel
def cuts41619 : List PrefixCut := [⟨53,246667537,246667682⟩,
⟨64,295598282,295598457⟩]
theorem checked41619 : checkPrefixCuts (2^48) 5459017729 10 Manual.Count131072.C041619.packed 64 cuts41619 = true := by
 decide +kernel
def pointBounds41619 : List (Nat × Nat × Nat) := [(5459126272,109364649792780,109365035592943)]
theorem point_links_checked41619 : (cuts41619.take 1).map (fun c => (5459017729-1+2*2^10*c.k,109364403125243+c.lower,109364788925261+c.upper)) = pointBounds41619 := by
 decide +kernel
def cuts41620 : List PrefixCut := [⟨64,303015728,303015908⟩]
theorem checked41620 : checkPrefixCuts (2^48) 5459148801 10 Manual.Count131072.C041620.packed 64 cuts41620 = true := by
 decide +kernel
def cuts41621 : List PrefixCut := [⟨9,41504904,41504931⟩,
⟨64,304916124,304916308⟩]
theorem checked41621 : checkPrefixCuts (2^48) 5459279873 10 Manual.Count131072.C041621.packed 64 cuts41621 = true := by
 decide +kernel
def pointBounds41621 : List (Nat × Nat × Nat) := [(5459298304,109365043244157,109365429044557)]
theorem point_links_checked41621 : (cuts41621.take 1).map (fun c => (5459279873-1+2*2^10*c.k,109365001739253+c.lower,109365387539626+c.upper)) = pointBounds41621 := by
 decide +kernel
def cuts41622 : List PrefixCut := [⟨29,139566053,139566133⟩,
⟨64,305475980,305476158⟩]
theorem checked41622 : checkPrefixCuts (2^48) 5459410945 10 Manual.Count131072.C041622.packed 64 cuts41622 = true := by
 decide +kernel
def pointBounds41622 : List (Nat × Nat × Nat) := [(5459470336,109365446221430,109365832022067)]
theorem point_links_checked41622 : (cuts41622.take 1).map (fun c => (5459410945-1+2*2^10*c.k,109365306655377+c.lower,109365692455934+c.upper)) = pointBounds41622 := by
 decide +kernel
def cuts41623 : List PrefixCut := [⟨49,232105249,232105382⟩,
⟨64,302065934,302066109⟩]
theorem checked41623 : checkPrefixCuts (2^48) 5459542017 10 Manual.Count131072.C041623.packed 64 cuts41623 = true := by
 decide +kernel
def pointBounds41623 : List (Nat × Nat × Nat) := [(5459642368,109365844236606,109366230037474)]
theorem point_links_checked41623 : (cuts41623.take 1).map (fun c => (5459542017-1+2*2^10*c.k,109365612131357+c.lower,109365997932092+c.upper)) = pointBounds41623 := by
 decide +kernel
def cuts41624 : List PrefixCut := [⟨64,305615940,305616122⟩]
theorem checked41624 : checkPrefixCuts (2^48) 5459673089 10 Manual.Count131072.C041624.packed 64 cuts41624 = true := by
 decide +kernel
def cuts41625 : List PrefixCut := [⟨5,23405507,23405520⟩,
⟨64,307361435,307361619⟩]
theorem checked41625 : checkPrefixCuts (2^48) 5459804161 10 Manual.Count131072.C041625.packed 64 cuts41625 = true := by
 decide +kernel
def pointBounds41625 : List (Nat × Nat × Nat) := [(5459814400,109366243218738,109366629019843)]
theorem point_links_checked41625 : (cuts41625.take 1).map (fun c => (5459804161-1+2*2^10*c.k,109366219813231+c.lower,109366605614323+c.upper)) = pointBounds41625 := by
 decide +kernel
def cuts41626 : List PrefixCut := [⟨25,114859086,114859156⟩,
⟨64,295857917,295858093⟩]
theorem checked41626 : checkPrefixCuts (2^48) 5459935233 10 Manual.Count131072.C041626.packed 64 cuts41626 = true := by
 decide +kernel
def pointBounds41626 : List (Nat × Nat × Nat) := [(5459986432,109366642033752,109367027835098)]
theorem point_links_checked41626 : (cuts41626.take 1).map (fun c => (5459935233-1+2*2^10*c.k,109366527174666+c.lower,109366912975942+c.upper)) = pointBounds41626 := by
 decide +kernel
def cuts41627 : List PrefixCut := [⟨45,214401093,214401218⟩,
⟨64,304408262,304408440⟩]
theorem checked41627 : checkPrefixCuts (2^48) 5460066305 10 Manual.Count131072.C041627.packed 64 cuts41627 = true := by
 decide +kernel
def pointBounds41627 : List (Nat × Nat × Nat) := [(5460158464,109367037433676,109367423235253)]
theorem point_links_checked41627 : (cuts41627.take 1).map (fun c => (5460066305-1+2*2^10*c.k,109366823032583+c.lower,109367208834035+c.upper)) = pointBounds41627 := by
 decide +kernel
def cuts41628 : List PrefixCut := [⟨64,306411401,306411582⟩]
theorem checked41628 : checkPrefixCuts (2^48) 5460197377 10 Manual.Count131072.C041628.packed 64 cuts41628 = true := by
 decide +kernel
def cuts41629 : List PrefixCut := [⟨1,4381671,4381673⟩,
⟨64,297486145,297486318⟩]
theorem checked41629 : checkPrefixCuts (2^48) 5460328449 10 Manual.Count131072.C041629.packed 64 cuts41629 = true := by
 decide +kernel
def pointBounds41629 : List (Nat × Nat × Nat) := [(5460330496,109367438233917,109367824035730)]
theorem point_links_checked41629 : (cuts41629.take 1).map (fun c => (5460328449-1+2*2^10*c.k,109367433852246+c.lower,109367819654057+c.upper)) = pointBounds41629 := by
 decide +kernel
def cuts41630 : List PrefixCut := [⟨21,97425035,97425093⟩,
⟨64,302221345,302221525⟩]
theorem checked41630 : checkPrefixCuts (2^48) 5460459521 10 Manual.Count131072.C041630.packed 64 cuts41630 = true := by
 decide +kernel
def pointBounds41630 : List (Nat × Nat × Nat) := [(5460502528,109367828763426,109368214565468)]
theorem point_links_checked41630 : (cuts41630.take 1).map (fun c => (5460459521-1+2*2^10*c.k,109367731338391+c.lower,109368117140375+c.upper)) = pointBounds41630 := by
 decide +kernel
def cuts41631 : List PrefixCut := [⟨41,192421986,192422100⟩,
⟨64,298812080,298812256⟩]
theorem checked41631 : checkPrefixCuts (2^48) 5460590593 10 Manual.Count131072.C041631.packed 64 cuts41631 = true := by
 decide +kernel
def pointBounds41631 : List (Nat × Nat × Nat) := [(5460674560,109368225981722,109368611784000)]
theorem point_links_checked41631 : (cuts41631.take 1).map (fun c => (5460590593-1+2*2^10*c.k,109368033559736+c.lower,109368419361900+c.upper)) = pointBounds41631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000050
