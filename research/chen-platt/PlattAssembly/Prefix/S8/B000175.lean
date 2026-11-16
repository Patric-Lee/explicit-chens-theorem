import PlattAssemblyKernel
import PlattCertificates.Count131072.C075600
import PlattCertificates.Count131072.C075601
import PlattCertificates.Count131072.C075602
import PlattCertificates.Count131072.C075603
import PlattCertificates.Count131072.C075604
import PlattCertificates.Count131072.C075605
import PlattCertificates.Count131072.C075606
import PlattCertificates.Count131072.C075607
import PlattCertificates.Count131072.C075608
import PlattCertificates.Count131072.C075609
import PlattCertificates.Count131072.C075610
import PlattCertificates.Count131072.C075611
import PlattCertificates.Count131072.C075612
import PlattCertificates.Count131072.C075613
import PlattCertificates.Count131072.C075614
import PlattCertificates.Count131072.C075615
import PlattCertificates.Count131072.C075616
import PlattCertificates.Count131072.C075617
import PlattCertificates.Count131072.C075618
import PlattCertificates.Count131072.C075619
import PlattCertificates.Count131072.C075620
import PlattCertificates.Count131072.C075621
import PlattCertificates.Count131072.C075622
import PlattCertificates.Count131072.C075623
import PlattCertificates.Count131072.C075624
import PlattCertificates.Count131072.C075625
import PlattCertificates.Count131072.C075626
import PlattCertificates.Count131072.C075627
import PlattCertificates.Count131072.C075628
import PlattCertificates.Count131072.C075629
import PlattCertificates.Count131072.C075630
import PlattCertificates.Count131072.C075631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000175
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75600 : List PrefixCut := [⟨64,160286413,160286507⟩]
theorem checked75600 : checkPrefixCuts (2^48) 9912975361 10 Manual.Count131072.C075600.packed 64 cuts75600 = true := by
 decide +kernel
def cuts75601 : List PrefixCut := [⟨19,47787373,47787402⟩,
⟨64,161448442,161448543⟩]
theorem checked75601 : checkPrefixCuts (2^48) 9913106433 10 Manual.Count131072.C075601.packed 64 cuts75601 = true := by
 decide +kernel
def pointBounds75601 : List (Nat × Nat × Nat) := [(9913145344,116756337768773,116756727834792)]
theorem point_links_checked75601 : (cuts75601.take 1).map (fun c => (9913106433-1+2*2^10*c.k,116756289981400+c.lower,116756680047390+c.upper)) = pointBounds75601 := by
 decide +kernel
def cuts75602 : List PrefixCut := [⟨64,160736464,160736562⟩]
theorem checked75602 : checkPrefixCuts (2^48) 9913237505 10 Manual.Count131072.C075602.packed 64 cuts75602 = true := by
 decide +kernel
def cuts75603 : List PrefixCut := [⟨43,107270043,107270106⟩,
⟨64,161018279,161018374⟩]
theorem checked75603 : checkPrefixCuts (2^48) 9913368577 10 Manual.Count131072.C075603.packed 64 cuts75603 = true := by
 decide +kernel
def pointBounds75603 : List (Nat × Nat × Nat) := [(9913456640,116756719436349,116757109502601)]
theorem point_links_checked75603 : (cuts75603.take 1).map (fun c => (9913368577-1+2*2^10*c.k,116756612166306+c.lower,116757002232495+c.upper)) = pointBounds75603 := by
 decide +kernel
def cuts75604 : List PrefixCut := [⟨64,162237034,162237126⟩]
theorem checked75604 : checkPrefixCuts (2^48) 9913499649 10 Manual.Count131072.C075604.packed 64 cuts75604 = true := by
 decide +kernel
def cuts75605 : List PrefixCut := [⟨64,160730090,160730186⟩]
theorem checked75605 : checkPrefixCuts (2^48) 9913630721 10 Manual.Count131072.C075605.packed 64 cuts75605 = true := by
 decide +kernel
def cuts75606 : List PrefixCut := [⟨3,7893068,7893073⟩,
⟨64,162317931,162318037⟩]
theorem checked75606 : checkPrefixCuts (2^48) 9913761793 10 Manual.Count131072.C075606.packed 64 cuts75606 = true := by
 decide +kernel
def pointBounds75606 : List (Nat × Nat × Nat) := [(9913767936,116757104044777,116757494111254)]
theorem point_links_checked75606 : (cuts75606.take 1).map (fun c => (9913761793-1+2*2^10*c.k,116757096151709+c.lower,116757486218181+c.upper)) = pointBounds75606 := by
 decide +kernel
def cuts75607 : List PrefixCut := [⟨64,161123332,161123432⟩]
theorem checked75607 : checkPrefixCuts (2^48) 9913892865 10 Manual.Count131072.C075607.packed 64 cuts75607 = true := by
 decide +kernel
def cuts75608 : List PrefixCut := [⟨27,67742140,67742187⟩,
⟨64,161830984,161831085⟩]
theorem checked75608 : checkPrefixCuts (2^48) 9914023937 10 Manual.Count131072.C075608.packed 64 cuts75608 = true := by
 decide +kernel
def pointBounds75608 : List (Nat × Nat × Nat) := [(9914079232,116757487335112,116757877401837)]
theorem point_links_checked75608 : (cuts75608.take 1).map (fun c => (9914023937-1+2*2^10*c.k,116757419592972+c.lower,116757809659650+c.upper)) = pointBounds75608 := by
 decide +kernel
def cuts75609 : List PrefixCut := [⟨64,160891936,160892032⟩]
theorem checked75609 : checkPrefixCuts (2^48) 9914155009 10 Manual.Count131072.C075609.packed 64 cuts75609 = true := by
 decide +kernel
def cuts75610 : List PrefixCut := [⟨51,128496252,128496325⟩,
⟨64,159583850,159583945⟩]
theorem checked75610 : checkPrefixCuts (2^48) 9914286081 10 Manual.Count131072.C075610.packed 64 cuts75610 = true := by
 decide +kernel
def pointBounds75610 : List (Nat × Nat × Nat) := [(9914390528,116757870812144,116758260879092)]
theorem point_links_checked75610 : (cuts75610.take 1).map (fun c => (9914286081-1+2*2^10*c.k,116757742315892+c.lower,116758132382767+c.upper)) = pointBounds75610 := by
 decide +kernel
def cuts75611 : List PrefixCut := [⟨64,162193640,162193744⟩]
theorem checked75611 : checkPrefixCuts (2^48) 9914417153 10 Manual.Count131072.C075611.packed 64 cuts75611 = true := by
 decide +kernel
def cuts75612 : List PrefixCut := [⟨64,162219890,162219991⟩]
theorem checked75612 : checkPrefixCuts (2^48) 9914548225 10 Manual.Count131072.C075612.packed 64 cuts75612 = true := by
 decide +kernel
def cuts75613 : List PrefixCut := [⟨11,27821885,27821905⟩,
⟨64,165993544,165993651⟩]
theorem checked75613 : checkPrefixCuts (2^48) 9914679297 10 Manual.Count131072.C075613.packed 64 cuts75613 = true := by
 decide +kernel
def pointBounds75613 : List (Nat × Nat × Nat) := [(9914701824,116758254135157,116758644202352)]
theorem point_links_checked75613 : (cuts75613.take 1).map (fun c => (9914679297-1+2*2^10*c.k,116758226313272+c.lower,116758616380447+c.upper)) = pointBounds75613 := by
 decide +kernel
def cuts75614 : List PrefixCut := [⟨64,162187201,162187305⟩]
theorem checked75614 : checkPrefixCuts (2^48) 9914810369 10 Manual.Count131072.C075614.packed 64 cuts75614 = true := by
 decide +kernel
def cuts75615 : List PrefixCut := [⟨35,87494465,87494518⟩,
⟨64,160339794,160339890⟩]
theorem checked75615 : checkPrefixCuts (2^48) 9914941441 10 Manual.Count131072.C075615.packed 64 cuts75615 = true := by
 decide +kernel
def pointBounds75615 : List (Nat × Nat × Nat) := [(9915013120,116758641988482,116759032055921)]
theorem point_links_checked75615 : (cuts75615.take 1).map (fun c => (9914941441-1+2*2^10*c.k,116758554494017+c.lower,116758944561403+c.upper)) = pointBounds75615 := by
 decide +kernel
def cuts75616 : List PrefixCut := [⟨64,161416429,161416528⟩]
theorem checked75616 : checkPrefixCuts (2^48) 9915072513 10 Manual.Count131072.C075616.packed 64 cuts75616 = true := by
 decide +kernel
def cuts75617 : List PrefixCut := [⟨59,149406253,149406341⟩,
⟨64,162521440,162521536⟩]
theorem checked75617 : checkPrefixCuts (2^48) 9915203585 10 Manual.Count131072.C075617.packed 64 cuts75617 = true := by
 decide +kernel
def pointBounds75617 : List (Nat × Nat × Nat) := [(9915324416,116759025656493,116759415724162)]
theorem point_links_checked75617 : (cuts75617.take 1).map (fun c => (9915203585-1+2*2^10*c.k,116758876250240+c.lower,116759266317821+c.upper)) = pointBounds75617 := by
 decide +kernel
def cuts75618 : List PrefixCut := [⟨64,159936010,159936114⟩]
theorem checked75618 : checkPrefixCuts (2^48) 9915334657 10 Manual.Count131072.C075618.packed 64 cuts75618 = true := by
 decide +kernel
def cuts75619 : List PrefixCut := [⟨64,162942949,162943043⟩]
theorem checked75619 : checkPrefixCuts (2^48) 9915465729 10 Manual.Count131072.C075619.packed 64 cuts75619 = true := by
 decide +kernel
def cuts75620 : List PrefixCut := [⟨19,48541821,48541850⟩,
⟨64,161038878,161038979⟩]
theorem checked75620 : checkPrefixCuts (2^48) 9915596801 10 Manual.Count131072.C075620.packed 64 cuts75620 = true := by
 decide +kernel
def pointBounds75620 : List (Nat × Nat × Nat) := [(9915635712,116759410192460,116759800260364)]
theorem point_links_checked75620 : (cuts75620.take 1).map (fun c => (9915596801-1+2*2^10*c.k,116759361650639+c.lower,116759751718514+c.upper)) = pointBounds75620 := by
 decide +kernel
def cuts75621 : List PrefixCut := [⟨64,161462547,161462643⟩]
theorem checked75621 : checkPrefixCuts (2^48) 9915727873 10 Manual.Count131072.C075621.packed 64 cuts75621 = true := by
 decide +kernel
def cuts75622 : List PrefixCut := [⟨43,109003039,109003100⟩,
⟨64,162709391,162709484⟩]
theorem checked75622 : checkPrefixCuts (2^48) 9915858945 10 Manual.Count131072.C075622.packed 64 cuts75622 = true := by
 decide +kernel
def pointBounds75622 : List (Nat × Nat × Nat) := [(9915947008,116759793155103,116760183223236)]
theorem point_links_checked75622 : (cuts75622.take 1).map (fun c => (9915858945-1+2*2^10*c.k,116759684152064+c.lower,116760074220136+c.upper)) = pointBounds75622 := by
 decide +kernel
def cuts75623 : List PrefixCut := [⟨64,160606697,160606800⟩]
theorem checked75623 : checkPrefixCuts (2^48) 9915990017 10 Manual.Count131072.C075623.packed 64 cuts75623 = true := by
 decide +kernel
def cuts75624 : List PrefixCut := [⟨64,159014997,159015095⟩]
theorem checked75624 : checkPrefixCuts (2^48) 9916121089 10 Manual.Count131072.C075624.packed 64 cuts75624 = true := by
 decide +kernel
def cuts75625 : List PrefixCut := [⟨3,7919471,7919475⟩,
⟨64,162788107,162788204⟩]
theorem checked75625 : checkPrefixCuts (2^48) 9916252161 10 Manual.Count131072.C075625.packed 64 cuts75625 = true := by
 decide +kernel
def pointBounds75625 : List (Nat × Nat × Nat) := [(9916258304,116760174402620,116760564470990)]
theorem point_links_checked75625 : (cuts75625.take 1).map (fun c => (9916252161-1+2*2^10*c.k,116760166483149+c.lower,116760556551515+c.upper)) = pointBounds75625 := by
 decide +kernel
def cuts75626 : List PrefixCut := [⟨64,161054479,161054581⟩]
theorem checked75626 : checkPrefixCuts (2^48) 9916383233 10 Manual.Count131072.C075626.packed 64 cuts75626 = true := by
 decide +kernel
def cuts75627 : List PrefixCut := [⟨27,67327746,67327786⟩,
⟨64,161307805,161307903⟩]
theorem checked75627 : checkPrefixCuts (2^48) 9916514305 10 Manual.Count131072.C075627.packed 64 cuts75627 = true := by
 decide +kernel
def pointBounds75627 : List (Nat × Nat × Nat) := [(9916569600,116760557653481,116760947722086)]
theorem point_links_checked75627 : (cuts75627.take 1).map (fun c => (9916514305-1+2*2^10*c.k,116760490325735+c.lower,116760880394300+c.upper)) = pointBounds75627 := by
 decide +kernel
def cuts75628 : List PrefixCut := [⟨64,160255473,160255574⟩]
theorem checked75628 : checkPrefixCuts (2^48) 9916645377 10 Manual.Count131072.C075628.packed 64 cuts75628 = true := by
 decide +kernel
def cuts75629 : List PrefixCut := [⟨51,130819819,130819900⟩,
⟨64,164766332,164766434⟩]
theorem checked75629 : checkPrefixCuts (2^48) 9916776449 10 Manual.Count131072.C075629.packed 64 cuts75629 = true := by
 decide +kernel
def pointBounds75629 : List (Nat × Nat × Nat) := [(9916880896,116760942708832,116761332777677)]
theorem point_links_checked75629 : (cuts75629.take 1).map (fun c => (9916776449-1+2*2^10*c.k,116760811889013+c.lower,116761201957777+c.upper)) = pointBounds75629 := by
 decide +kernel
def cuts75630 : List PrefixCut := [⟨64,160960822,160960921⟩]
theorem checked75630 : checkPrefixCuts (2^48) 9916907521 10 Manual.Count131072.C075630.packed 64 cuts75630 = true := by
 decide +kernel
def cuts75631 : List PrefixCut := [⟨64,163229314,163229413⟩]
theorem checked75631 : checkPrefixCuts (2^48) 9917038593 10 Manual.Count131072.C075631.packed 64 cuts75631 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000175
