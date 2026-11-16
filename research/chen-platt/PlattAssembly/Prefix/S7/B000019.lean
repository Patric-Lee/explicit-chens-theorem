import PlattAssemblyKernel
import PlattCertificates.Count131072.C060608
import PlattCertificates.Count131072.C060609
import PlattCertificates.Count131072.C060610
import PlattCertificates.Count131072.C060611
import PlattCertificates.Count131072.C060612
import PlattCertificates.Count131072.C060613
import PlattCertificates.Count131072.C060614
import PlattCertificates.Count131072.C060615
import PlattCertificates.Count131072.C060616
import PlattCertificates.Count131072.C060617
import PlattCertificates.Count131072.C060618
import PlattCertificates.Count131072.C060619
import PlattCertificates.Count131072.C060620
import PlattCertificates.Count131072.C060621
import PlattCertificates.Count131072.C060622
import PlattCertificates.Count131072.C060623
import PlattCertificates.Count131072.C060624
import PlattCertificates.Count131072.C060625
import PlattCertificates.Count131072.C060626
import PlattCertificates.Count131072.C060627
import PlattCertificates.Count131072.C060628
import PlattCertificates.Count131072.C060629
import PlattCertificates.Count131072.C060630
import PlattCertificates.Count131072.C060631
import PlattCertificates.Count131072.C060632
import PlattCertificates.Count131072.C060633
import PlattCertificates.Count131072.C060634
import PlattCertificates.Count131072.C060635
import PlattCertificates.Count131072.C060636
import PlattCertificates.Count131072.C060637
import PlattCertificates.Count131072.C060638
import PlattCertificates.Count131072.C060639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60608 : List PrefixCut := [⟨56,178595573,178595676⟩,
⟨64,203208482,203208599⟩]
theorem checked60608 : checkPrefixCuts (2^48) 7947943937 10 Manual.Count131072.C060608.packed 64 cuts60608 = true := by
 decide +kernel
def pointBounds60608 : List (Nat × Nat × Nat) := [(7948058624,114041429187538,114041817665991)]
theorem point_links_checked60608 : (cuts60608.take 1).map (fun c => (7947943937-1+2*2^10*c.k,114041250591965+c.lower,114041639070315+c.upper)) = pointBounds60608 := by
 decide +kernel
def cuts60609 : List PrefixCut := [⟨64,203240560,203240678⟩]
theorem checked60609 : checkPrefixCuts (2^48) 7948075009 10 Manual.Count131072.C060609.packed 64 cuts60609 = true := by
 decide +kernel
def cuts60610 : List PrefixCut := [⟨50,159466591,159466680⟩,
⟨64,203945467,203945580⟩]
theorem checked60610 : checkPrefixCuts (2^48) 7948206081 10 Manual.Count131072.C060610.packed 64 cuts60610 = true := by
 decide +kernel
def pointBounds60610 : List (Nat × Nat × Nat) := [(7948308480,114041816507598,114042204986272)]
theorem point_links_checked60610 : (cuts60610.take 1).map (fun c => (7948206081-1+2*2^10*c.k,114041657041007+c.lower,114042045519592+c.upper)) = pointBounds60610 := by
 decide +kernel
def cuts60611 : List PrefixCut := [⟨64,201569449,201569565⟩]
theorem checked60611 : checkPrefixCuts (2^48) 7948337153 10 Manual.Count131072.C060611.packed 64 cuts60611 = true := by
 decide +kernel
def cuts60612 : List PrefixCut := [⟨44,141755314,141755390⟩,
⟨64,204646988,204647099⟩]
theorem checked60612 : checkPrefixCuts (2^48) 7948468225 10 Manual.Count131072.C060612.packed 64 cuts60612 = true := by
 decide +kernel
def pointBounds60612 : List (Nat × Nat × Nat) := [(7948558336,114042204311237,114042592790127)]
theorem point_links_checked60612 : (cuts60612.take 1).map (fun c => (7948468225-1+2*2^10*c.k,114042062555923+c.lower,114042451034737+c.upper)) = pointBounds60612 := by
 decide +kernel
def cuts60613 : List PrefixCut := [⟨64,203687488,203687602⟩]
theorem checked60613 : checkPrefixCuts (2^48) 7948599297 10 Manual.Count131072.C060613.packed 64 cuts60613 = true := by
 decide +kernel
def cuts60614 : List PrefixCut := [⟨38,118733519,118733584⟩,
⟨64,201205361,201205471⟩]
theorem checked60614 : checkPrefixCuts (2^48) 7948730369 10 Manual.Count131072.C060614.packed 64 cuts60614 = true := by
 decide +kernel
def pointBounds60614 : List (Nat × Nat × Nat) := [(7948808192,114042589623918,114042978103022)]
theorem point_links_checked60614 : (cuts60614.take 1).map (fun c => (7948730369-1+2*2^10*c.k,114042470890399+c.lower,114042859369438+c.upper)) = pointBounds60614 := by
 decide +kernel
def cuts60615 : List PrefixCut := [⟨64,202512221,202512341⟩]
theorem checked60615 : checkPrefixCuts (2^48) 7948861441 10 Manual.Count131072.C060615.packed 64 cuts60615 = true := by
 decide +kernel
def cuts60616 : List PrefixCut := [⟨32,101874534,101874595⟩,
⟨64,204066921,204067041⟩]
theorem checked60616 : checkPrefixCuts (2^48) 7948992513 10 Manual.Count131072.C060616.packed 64 cuts60616 = true := by
 decide +kernel
def pointBounds60616 : List (Nat × Nat × Nat) := [(7949058048,114042976482515,114043364961845)]
theorem point_links_checked60616 : (cuts60616.take 1).map (fun c => (7948992513-1+2*2^10*c.k,114042874607981+c.lower,114043263087250+c.upper)) = pointBounds60616 := by
 decide +kernel
def cuts60617 : List PrefixCut := [⟨64,205409113,205409229⟩]
theorem checked60617 : checkPrefixCuts (2^48) 7949123585 10 Manual.Count131072.C060617.packed 64 cuts60617 = true := by
 decide +kernel
def cuts60618 : List PrefixCut := [⟨26,83281610,83281657⟩,
⟨64,203812336,203812452⟩]
theorem checked60618 : checkPrefixCuts (2^48) 7949254657 10 Manual.Count131072.C060618.packed 64 cuts60618 = true := by
 decide +kernel
def pointBounds60618 : List (Nat × Nat × Nat) := [(7949307904,114043367365625,114043755845177)]
theorem point_links_checked60618 : (cuts60618.take 1).map (fun c => (7949254657-1+2*2^10*c.k,114043284084015+c.lower,114043672563520+c.upper)) = pointBounds60618 := by
 decide +kernel
def cuts60619 : List PrefixCut := [⟨64,204871209,204871322⟩]
theorem checked60619 : checkPrefixCuts (2^48) 7949385729 10 Manual.Count131072.C060619.packed 64 cuts60619 = true := by
 decide +kernel
def cuts60620 : List PrefixCut := [⟨20,62423792,62423829⟩,
⟨64,201433312,201433430⟩]
theorem checked60620 : checkPrefixCuts (2^48) 7949516801 10 Manual.Count131072.C060620.packed 64 cuts60620 = true := by
 decide +kernel
def pointBounds60620 : List (Nat × Nat × Nat) := [(7949557760,114043755191352,114044143671123)]
theorem point_links_checked60620 : (cuts60620.take 1).map (fun c => (7949516801-1+2*2^10*c.k,114043692767560+c.lower,114044081247294+c.upper)) = pointBounds60620 := by
 decide +kernel
def cuts60621 : List PrefixCut := [⟨64,206032883,206033004⟩]
theorem checked60621 : checkPrefixCuts (2^48) 7949647873 10 Manual.Count131072.C060621.packed 64 cuts60621 = true := by
 decide +kernel
def cuts60622 : List PrefixCut := [⟨14,44789309,44789332⟩,
⟨64,203515658,203515770⟩]
theorem checked60622 : checkPrefixCuts (2^48) 7949778945 10 Manual.Count131072.C060622.packed 64 cuts60622 = true := by
 decide +kernel
def pointBounds60622 : List (Nat × Nat × Nat) := [(7949807616,114044145023064,114044533503060)]
theorem point_links_checked60622 : (cuts60622.take 1).map (fun c => (7949778945-1+2*2^10*c.k,114044100233755+c.lower,114044488713728+c.upper)) = pointBounds60622 := by
 decide +kernel
def cuts60623 : List PrefixCut := [⟨64,203299852,203299974⟩]
theorem checked60623 : checkPrefixCuts (2^48) 7949910017 10 Manual.Count131072.C060623.packed 64 cuts60623 = true := by
 decide +kernel
def cuts60624 : List PrefixCut := [⟨8,25173259,25173273⟩,
⟨64,203756756,203756874⟩]
theorem checked60624 : checkPrefixCuts (2^48) 7950041089 10 Manual.Count131072.C060624.packed 64 cuts60624 = true := by
 decide +kernel
def pointBounds60624 : List (Nat × Nat × Nat) := [(7950057472,114044532222524,114044920702745)]
theorem point_links_checked60624 : (cuts60624.take 1).map (fun c => (7950041089-1+2*2^10*c.k,114044507049265+c.lower,114044895529472+c.upper)) = pointBounds60624 := by
 decide +kernel
def cuts60625 : List PrefixCut := [⟨64,204284480,204284598⟩]
theorem checked60625 : checkPrefixCuts (2^48) 7950172161 10 Manual.Count131072.C060625.packed 64 cuts60625 = true := by
 decide +kernel
def cuts60626 : List PrefixCut := [⟨2,6656006,6656010⟩,
⟨64,202900351,202900469⟩]
theorem checked60626 : checkPrefixCuts (2^48) 7950303233 10 Manual.Count131072.C060626.packed 64 cuts60626 = true := by
 decide +kernel
def pointBounds60626 : List (Nat × Nat × Nat) := [(7950307328,114044921746507,114045310226954)]
theorem point_links_checked60626 : (cuts60626.take 1).map (fun c => (7950303233-1+2*2^10*c.k,114044915090501+c.lower,114045303570944+c.upper)) = pointBounds60626 := by
 decide +kernel
def cuts60627 : List PrefixCut := [⟨60,190682922,190683026⟩,
⟨64,202649186,202649297⟩]
theorem checked60627 : checkPrefixCuts (2^48) 7950434305 10 Manual.Count131072.C060627.packed 64 cuts60627 = true := by
 decide +kernel
def pointBounds60627 : List (Nat × Nat × Nat) := [(7950557184,114045308673774,114045697154439)]
theorem point_links_checked60627 : (cuts60627.take 1).map (fun c => (7950434305-1+2*2^10*c.k,114045117990852+c.lower,114045506471413+c.upper)) = pointBounds60627 := by
 decide +kernel
def cuts60628 : List PrefixCut := [⟨64,206717174,206717292⟩]
theorem checked60628 : checkPrefixCuts (2^48) 7950565377 10 Manual.Count131072.C060628.packed 64 cuts60628 = true := by
 decide +kernel
def cuts60629 : List PrefixCut := [⟨54,169860215,169860316⟩,
⟨64,200058128,200058247⟩]
theorem checked60629 : checkPrefixCuts (2^48) 7950696449 10 Manual.Count131072.C060629.packed 64 cuts60629 = true := by
 decide +kernel
def pointBounds60629 : List (Nat × Nat × Nat) := [(7950807040,114045697217427,114046085698318)]
theorem point_links_checked60629 : (cuts60629.take 1).map (fun c => (7950696449-1+2*2^10*c.k,114045527357212+c.lower,114045915838002+c.upper)) = pointBounds60629 := by
 decide +kernel
def cuts60630 : List PrefixCut := [⟨64,201683320,201683439⟩]
theorem checked60630 : checkPrefixCuts (2^48) 7950827521 10 Manual.Count131072.C060630.packed 64 cuts60630 = true := by
 decide +kernel
def cuts60631 : List PrefixCut := [⟨48,152401989,152402077⟩,
⟨64,204759876,204759994⟩]
theorem checked60631 : checkPrefixCuts (2^48) 7950958593 10 Manual.Count131072.C060631.packed 64 cuts60631 = true := by
 decide +kernel
def pointBounds60631 : List (Nat × Nat × Nat) := [(7951056896,114046081500649,114046469981765)]
theorem point_links_checked60631 : (cuts60631.take 1).map (fun c => (7950958593-1+2*2^10*c.k,114045929098660+c.lower,114046317579688+c.upper)) = pointBounds60631 := by
 decide +kernel
def cuts60632 : List PrefixCut := [⟨64,204933512,204933629⟩]
theorem checked60632 : checkPrefixCuts (2^48) 7951089665 10 Manual.Count131072.C060632.packed 64 cuts60632 = true := by
 decide +kernel
def cuts60633 : List PrefixCut := [⟨42,135475876,135475952⟩,
⟨64,205638134,205638253⟩]
theorem checked60633 : checkPrefixCuts (2^48) 7951220737 10 Manual.Count131072.C060633.packed 64 cuts60633 = true := by
 decide +kernel
def pointBounds60633 : List (Nat × Nat × Nat) := [(7951306752,114046474267924,114046862749263)]
theorem point_links_checked60633 : (cuts60633.take 1).map (fun c => (7951220737-1+2*2^10*c.k,114046338792048+c.lower,114046727273311+c.upper)) = pointBounds60633 := by
 decide +kernel
def cuts60634 : List PrefixCut := [⟨64,205847144,205847260⟩]
theorem checked60634 : checkPrefixCuts (2^48) 7951351809 10 Manual.Count131072.C060634.packed 64 cuts60634 = true := by
 decide +kernel
def cuts60635 : List PrefixCut := [⟨36,115010962,115011027⟩,
⟨64,202162288,202162405⟩]
theorem checked60635 : checkPrefixCuts (2^48) 7951482881 10 Manual.Count131072.C060635.packed 64 cuts60635 = true := by
 decide +kernel
def pointBounds60635 : List (Nat × Nat × Nat) := [(7951556608,114046865288288,114047253769851)]
theorem point_links_checked60635 : (cuts60635.take 1).map (fun c => (7951482881-1+2*2^10*c.k,114046750277326+c.lower,114047138758824+c.upper)) = pointBounds60635 := by
 decide +kernel
def cuts60636 : List PrefixCut := [⟨64,205450972,205451091⟩]
theorem checked60636 : checkPrefixCuts (2^48) 7951613953 10 Manual.Count131072.C060636.packed 64 cuts60636 = true := by
 decide +kernel
def cuts60637 : List PrefixCut := [⟨30,95149124,95149178⟩,
⟨64,204562639,204562756⟩]
theorem checked60637 : checkPrefixCuts (2^48) 7951745025 10 Manual.Count131072.C060637.packed 64 cuts60637 = true := by
 decide +kernel
def pointBounds60637 : List (Nat × Nat × Nat) := [(7951806464,114047253039710,114047641521498)]
theorem point_links_checked60637 : (cuts60637.take 1).map (fun c => (7951745025-1+2*2^10*c.k,114047157890586+c.lower,114047546372320+c.upper)) = pointBounds60637 := by
 decide +kernel
def cuts60638 : List PrefixCut := [⟨64,202931013,202931125⟩]
theorem checked60638 : checkPrefixCuts (2^48) 7951876097 10 Manual.Count131072.C060638.packed 64 cuts60638 = true := by
 decide +kernel
def cuts60639 : List PrefixCut := [⟨24,75465552,75465596⟩,
⟨64,201370224,201370341⟩]
theorem checked60639 : checkPrefixCuts (2^48) 7952007169 10 Manual.Count131072.C060639.packed 64 cuts60639 = true := by
 decide +kernel
def pointBounds60639 : List (Nat × Nat × Nat) := [(7952056320,114047640849790,114048029331797)]
theorem point_links_checked60639 : (cuts60639.take 1).map (fun c => (7952007169-1+2*2^10*c.k,114047565384238+c.lower,114047953866201+c.upper)) = pointBounds60639 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000019
