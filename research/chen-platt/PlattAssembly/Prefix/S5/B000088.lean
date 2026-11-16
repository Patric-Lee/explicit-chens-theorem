import PlattAssemblyKernel
import PlattCertificates.Count131072.C042816
import PlattCertificates.Count131072.C042817
import PlattCertificates.Count131072.C042818
import PlattCertificates.Count131072.C042819
import PlattCertificates.Count131072.C042820
import PlattCertificates.Count131072.C042821
import PlattCertificates.Count131072.C042822
import PlattCertificates.Count131072.C042823
import PlattCertificates.Count131072.C042824
import PlattCertificates.Count131072.C042825
import PlattCertificates.Count131072.C042826
import PlattCertificates.Count131072.C042827
import PlattCertificates.Count131072.C042828
import PlattCertificates.Count131072.C042829
import PlattCertificates.Count131072.C042830
import PlattCertificates.Count131072.C042831
import PlattCertificates.Count131072.C042832
import PlattCertificates.Count131072.C042833
import PlattCertificates.Count131072.C042834
import PlattCertificates.Count131072.C042835
import PlattCertificates.Count131072.C042836
import PlattCertificates.Count131072.C042837
import PlattCertificates.Count131072.C042838
import PlattCertificates.Count131072.C042839
import PlattCertificates.Count131072.C042840
import PlattCertificates.Count131072.C042841
import PlattCertificates.Count131072.C042842
import PlattCertificates.Count131072.C042843
import PlattCertificates.Count131072.C042844
import PlattCertificates.Count131072.C042845
import PlattCertificates.Count131072.C042846
import PlattCertificates.Count131072.C042847
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000088
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42816 : List PrefixCut := [⟨20,91320076,91320130⟩,
⟨64,293204225,293204396⟩]
theorem checked42816 : checkPrefixCuts (2^48) 5615910913 10 Manual.Count131072.C042816.packed 64 cuts42816 = true := by
 decide +kernel
def pointBounds42816 : List (Nat × Nat × Nat) := [(5615951872,109720034109167,109720420117323)]
theorem point_links_checked42816 : (cuts42816.take 1).map (fun c => (5615910913-1+2*2^10*c.k,109719942789091+c.lower,109720328797193+c.upper)) = pointBounds42816 := by
 decide +kernel
def cuts42817 : List PrefixCut := [⟨42,192959764,192959878⟩,
⟨64,293397893,293398066⟩]
theorem checked42817 : checkPrefixCuts (2^48) 5616041985 10 Manual.Count131072.C042817.packed 64 cuts42817 = true := by
 decide +kernel
def pointBounds42817 : List (Nat × Nat × Nat) := [(5616128000,109720428953080,109720814961467)]
theorem point_links_checked42817 : (cuts42817.take 1).map (fun c => (5616041985-1+2*2^10*c.k,109720235993316+c.lower,109720622001589+c.upper)) = pointBounds42817 := by
 decide +kernel
def cuts42818 : List PrefixCut := [⟨64,289231238,289231408⟩]
theorem checked42818 : checkPrefixCuts (2^48) 5616173057 10 Manual.Count131072.C042818.packed 64 cuts42818 = true := by
 decide +kernel
def pointBounds42818 : List (Nat × Nat × Nat) := [(5616304128,109720818622447,109721204631063)]
theorem point_links_checked42818 : (cuts42818.take 1).map (fun c => (5616173057-1+2*2^10*c.k,109720529391209+c.lower,109720915399655+c.upper)) = pointBounds42818 := by
 decide +kernel
def cuts42819 : List PrefixCut := [⟨64,292832886,292833052⟩]
theorem checked42819 : checkPrefixCuts (2^48) 5616304129 10 Manual.Count131072.C042819.packed 64 cuts42819 = true := by
 decide +kernel
def cuts42820 : List PrefixCut := [⟨22,98377884,98377941⟩,
⟨64,288716580,288716748⟩]
theorem checked42820 : checkPrefixCuts (2^48) 5616435201 10 Manual.Count131072.C042820.packed 64 cuts42820 = true := by
 decide +kernel
def pointBounds42820 : List (Nat × Nat × Nat) := [(5616480256,109721209833217,109721595842056)]
theorem point_links_checked42820 : (cuts42820.take 1).map (fun c => (5616435201-1+2*2^10*c.k,109721111455333+c.lower,109721497464115+c.upper)) = pointBounds42820 := by
 decide +kernel
def cuts42821 : List PrefixCut := [⟨44,198955418,198955533⟩,
⟨64,291065197,291065365⟩]
theorem checked42821 : checkPrefixCuts (2^48) 5616566273 10 Manual.Count131072.C042821.packed 64 cuts42821 = true := by
 decide +kernel
def pointBounds42821 : List (Nat × Nat × Nat) := [(5616656384,109721599127331,109721985136396)]
theorem point_links_checked42821 : (cuts42821.take 1).map (fun c => (5616566273-1+2*2^10*c.k,109721400171913+c.lower,109721786180863+c.upper)) = pointBounds42821 := by
 decide +kernel
def cuts42822 : List PrefixCut := [⟨64,288452513,288452686⟩]
theorem checked42822 : checkPrefixCuts (2^48) 5616697345 10 Manual.Count131072.C042822.packed 64 cuts42822 = true := by
 decide +kernel
def cuts42823 : List PrefixCut := [⟨2,9170636,9170641⟩,
⟨64,294058372,294058550⟩]
theorem checked42823 : checkPrefixCuts (2^48) 5616828417 10 Manual.Count131072.C042823.packed 64 cuts42823 = true := by
 decide +kernel
def pointBounds42823 : List (Nat × Nat × Nat) := [(5616832512,109721988860259,109722374869555)]
theorem point_links_checked42823 : (cuts42823.take 1).map (fun c => (5616828417-1+2*2^10*c.k,109721979689623+c.lower,109722365698914+c.upper)) = pointBounds42823 := by
 decide +kernel
def cuts42824 : List PrefixCut := [⟨24,110395400,110395464⟩,
⟨64,296306487,296306656⟩]
theorem checked42824 : checkPrefixCuts (2^48) 5616959489 10 Manual.Count131072.C042824.packed 64 cuts42824 = true := by
 decide +kernel
def pointBounds42824 : List (Nat × Nat × Nat) := [(5617008640,109722384143395,109722770152928)]
theorem point_links_checked42824 : (cuts42824.take 1).map (fun c => (5616959489-1+2*2^10*c.k,109722273747995+c.lower,109722659757464+c.upper)) = pointBounds42824 := by
 decide +kernel
def cuts42825 : List PrefixCut := [⟨46,212215937,212216063⟩,
⟨64,292541365,292541539⟩]
theorem checked42825 : checkPrefixCuts (2^48) 5617090561 10 Manual.Count131072.C042825.packed 64 cuts42825 = true := by
 decide +kernel
def pointBounds42825 : List (Nat × Nat × Nat) := [(5617184768,109722782270419,109723168280183)]
theorem point_links_checked42825 : (cuts42825.take 1).map (fun c => (5617090561-1+2*2^10*c.k,109722570054482+c.lower,109722956064120+c.upper)) = pointBounds42825 := by
 decide +kernel
def cuts42826 : List PrefixCut := [⟨64,288275275,288275446⟩]
theorem checked42826 : checkPrefixCuts (2^48) 5617221633 10 Manual.Count131072.C042826.packed 64 cuts42826 = true := by
 decide +kernel
def cuts42827 : List PrefixCut := [⟨4,18690308,18690320⟩,
⟨64,293579948,293580119⟩]
theorem checked42827 : checkPrefixCuts (2^48) 5617352705 10 Manual.Count131072.C042827.packed 64 cuts42827 = true := by
 decide +kernel
def pointBounds42827 : List (Nat × Nat × Nat) := [(5617360896,109723169561430,109723555571425)]
theorem point_links_checked42827 : (cuts42827.take 1).map (fun c => (5617352705-1+2*2^10*c.k,109723150871122+c.lower,109723536881105+c.upper)) = pointBounds42827 := by
 decide +kernel
def cuts42828 : List PrefixCut := [⟨26,117500210,117500275⟩,
⟨64,292220222,292220393⟩]
theorem checked42828 : checkPrefixCuts (2^48) 5617483777 10 Manual.Count131072.C042828.packed 64 cuts42828 = true := by
 decide +kernel
def pointBounds42828 : List (Nat × Nat × Nat) := [(5617537024,109723561951280,109723947961499)]
theorem point_links_checked42828 : (cuts42828.take 1).map (fun c => (5617483777-1+2*2^10*c.k,109723444451070+c.lower,109723830461224+c.upper)) = pointBounds42828 := by
 decide +kernel
def cuts42829 : List PrefixCut := [⟨48,217206589,217206718⟩,
⟨64,289908570,289908744⟩]
theorem checked42829 : checkPrefixCuts (2^48) 5617614849 10 Manual.Count131072.C042829.packed 64 cuts42829 = true := by
 decide +kernel
def pointBounds42829 : List (Nat × Nat × Nat) := [(5617713152,109723953877881,109724339888335)]
theorem point_links_checked42829 : (cuts42829.take 1).map (fun c => (5617614849-1+2*2^10*c.k,109723736671292+c.lower,109724122681617+c.upper)) = pointBounds42829 := by
 decide +kernel
def cuts42830 : List PrefixCut := [⟨64,292858003,292858166⟩]
theorem checked42830 : checkPrefixCuts (2^48) 5617745921 10 Manual.Count131072.C042830.packed 64 cuts42830 = true := by
 decide +kernel
def cuts42831 : List PrefixCut := [⟨6,27105926,27105940⟩,
⟨64,293151741,293151906⟩]
theorem checked42831 : checkPrefixCuts (2^48) 5617876993 10 Manual.Count131072.C042831.packed 64 cuts42831 = true := by
 decide +kernel
def pointBounds42831 : List (Nat × Nat × Nat) := [(5617889280,109724346543791,109724732554467)]
theorem point_links_checked42831 : (cuts42831.take 1).map (fun c => (5617876993-1+2*2^10*c.k,109724319437865+c.lower,109724705448527+c.upper)) = pointBounds42831 := by
 decide +kernel
def cuts42832 : List PrefixCut := [⟨28,128511642,128511717⟩,
⟨64,293896432,293896606⟩]
theorem checked42832 : checkPrefixCuts (2^48) 5618008065 10 Manual.Count131072.C042832.packed 64 cuts42832 = true := by
 decide +kernel
def pointBounds42832 : List (Nat × Nat × Nat) := [(5618065408,109724741101248,109725127112150)]
theorem point_links_checked42832 : (cuts42832.take 1).map (fun c => (5618008065-1+2*2^10*c.k,109724612589606+c.lower,109724998600433+c.upper)) = pointBounds42832 := by
 decide +kernel
def cuts42833 : List PrefixCut := [⟨50,231414817,231414955⟩,
⟨64,293538877,293539050⟩]
theorem checked42833 : checkPrefixCuts (2^48) 5618139137 10 Manual.Count131072.C042833.packed 64 cuts42833 = true := by
 decide +kernel
def pointBounds42833 : List (Nat × Nat × Nat) := [(5618241536,109725137900855,109725523911994)]
theorem point_links_checked42833 : (cuts42833.take 1).map (fun c => (5618139137-1+2*2^10*c.k,109724906486038+c.lower,109725292497039+c.upper)) = pointBounds42833 := by
 decide +kernel
def cuts42834 : List PrefixCut := [⟨64,292079109,292079276⟩]
theorem checked42834 : checkPrefixCuts (2^48) 5618270209 10 Manual.Count131072.C042834.packed 64 cuts42834 = true := by
 decide +kernel
def cuts42835 : List PrefixCut := [⟨8,38776378,38776400⟩,
⟨64,296781577,296781751⟩]
theorem checked42835 : checkPrefixCuts (2^48) 5618401281 10 Manual.Count131072.C042835.packed 64 cuts42835 = true := by
 decide +kernel
def pointBounds42835 : List (Nat × Nat × Nat) := [(5618417664,109725530880402,109725916891765)]
theorem point_links_checked42835 : (cuts42835.take 1).map (fun c => (5618401281-1+2*2^10*c.k,109725492104024+c.lower,109725878115365+c.upper)) = pointBounds42835 := by
 decide +kernel
def cuts42836 : List PrefixCut := [⟨30,139420819,139420898⟩,
⟨64,295171546,295171712⟩]
theorem checked42836 : checkPrefixCuts (2^48) 5618532353 10 Manual.Count131072.C042836.packed 64 cuts42836 = true := by
 decide +kernel
def pointBounds42836 : List (Nat × Nat × Nat) := [(5618593792,109725928306420,109726314318014)]
theorem point_links_checked42836 : (cuts42836.take 1).map (fun c => (5618532353-1+2*2^10*c.k,109725788885601+c.lower,109726174897116+c.upper)) = pointBounds42836 := by
 decide +kernel
def cuts42837 : List PrefixCut := [⟨52,234899885,234900018⟩,
⟨64,288752394,288752559⟩]
theorem checked42837 : checkPrefixCuts (2^48) 5618663425 10 Manual.Count131072.C042837.packed 64 cuts42837 = true := by
 decide +kernel
def pointBounds42837 : List (Nat × Nat × Nat) := [(5618769920,109726318957032,109726704968846)]
theorem point_links_checked42837 : (cuts42837.take 1).map (fun c => (5618663425-1+2*2^10*c.k,109726084057147+c.lower,109726470068828+c.upper)) = pointBounds42837 := by
 decide +kernel
def cuts42838 : List PrefixCut := [⟨64,291651136,291651305⟩]
theorem checked42838 : checkPrefixCuts (2^48) 5618794497 10 Manual.Count131072.C042838.packed 64 cuts42838 = true := by
 decide +kernel
def cuts42839 : List PrefixCut := [⟨10,43982523,43982547⟩,
⟨64,292996844,292997007⟩]
theorem checked42839 : checkPrefixCuts (2^48) 5618925569 10 Manual.Count131072.C042839.packed 64 cuts42839 = true := by
 decide +kernel
def pointBounds42839 : List (Nat × Nat × Nat) := [(5618946048,109726708443200,109727094455239)]
theorem point_links_checked42839 : (cuts42839.take 1).map (fun c => (5618925569-1+2*2^10*c.k,109726664460677+c.lower,109727050472692+c.upper)) = pointBounds42839 := by
 decide +kernel
def cuts42840 : List PrefixCut := [⟨32,146871549,146871633⟩,
⟨64,290435320,290435489⟩]
theorem checked42840 : checkPrefixCuts (2^48) 5619056641 10 Manual.Count131072.C042840.packed 64 cuts42840 = true := by
 decide +kernel
def pointBounds42840 : List (Nat × Nat × Nat) := [(5619122176,109727104329070,109727490341332)]
theorem point_links_checked42840 : (cuts42840.take 1).map (fun c => (5619056641-1+2*2^10*c.k,109726957457521+c.lower,109727343469699+c.upper)) = pointBounds42840 := by
 decide +kernel
def cuts42841 : List PrefixCut := [⟨54,249654750,249654893⟩,
⟨64,295086979,295087151⟩]
theorem checked42841 : checkPrefixCuts (2^48) 5619187713 10 Manual.Count131072.C042841.packed 64 cuts42841 = true := by
 decide +kernel
def pointBounds42841 : List (Nat × Nat × Nat) := [(5619298304,109727497547591,109727883560081)]
theorem point_links_checked42841 : (cuts42841.take 1).map (fun c => (5619187713-1+2*2^10*c.k,109727247892841+c.lower,109727633905188+c.upper)) = pointBounds42841 := by
 decide +kernel
def cuts42842 : List PrefixCut := [⟨64,292976340,292976502⟩]
theorem checked42842 : checkPrefixCuts (2^48) 5619318785 10 Manual.Count131072.C042842.packed 64 cuts42842 = true := by
 decide +kernel
def cuts42843 : List PrefixCut := [⟨12,54396971,54397005⟩,
⟨64,294422080,294422262⟩]
theorem checked42843 : checkPrefixCuts (2^48) 5619449857 10 Manual.Count131072.C042843.packed 64 cuts42843 = true := by
 decide +kernel
def pointBounds42843 : List (Nat × Nat × Nat) := [(5619474432,109727890353131,109728276365846)]
theorem point_links_checked42843 : (cuts42843.take 1).map (fun c => (5619449857-1+2*2^10*c.k,109727835956160+c.lower,109728221968841+c.upper)) = pointBounds42843 := by
 decide +kernel
def cuts42844 : List PrefixCut := [⟨34,156224241,156224331⟩,
⟨64,292862509,292862681⟩]
theorem checked42844 : checkPrefixCuts (2^48) 5619580929 10 Manual.Count131072.C042844.packed 64 cuts42844 = true := by
 decide +kernel
def pointBounds42844 : List (Nat × Nat × Nat) := [(5619650560,109728286602481,109728672615434)]
theorem point_links_checked42844 : (cuts42844.take 1).map (fun c => (5619580929-1+2*2^10*c.k,109728130378240+c.lower,109728516391103+c.upper)) = pointBounds42844 := by
 decide +kernel
def cuts42845 : List PrefixCut := [⟨56,254289441,254289587⟩,
⟨64,292304694,292304862⟩]
theorem checked42845 : checkPrefixCuts (2^48) 5619712001 10 Manual.Count131072.C042845.packed 64 cuts42845 = true := by
 decide +kernel
def pointBounds42845 : List (Nat × Nat × Nat) := [(5619826688,109728677530190,109729063543371)]
theorem point_links_checked42845 : (cuts42845.take 1).map (fun c => (5619712001-1+2*2^10*c.k,109728423240749+c.lower,109728809253784+c.upper)) = pointBounds42845 := by
 decide +kernel
def cuts42846 : List PrefixCut := [⟨64,291346275,291346443⟩]
theorem checked42846 : checkPrefixCuts (2^48) 5619843073 10 Manual.Count131072.C042846.packed 64 cuts42846 = true := by
 decide +kernel
def cuts42847 : List PrefixCut := [⟨14,62705923,62705959⟩,
⟨64,290788562,290788733⟩]
theorem checked42847 : checkPrefixCuts (2^48) 5619974145 10 Manual.Count131072.C042847.packed 64 cuts42847 = true := by
 decide +kernel
def pointBounds42847 : List (Nat × Nat × Nat) := [(5620002816,109729069597641,109729455611048)]
theorem point_links_checked42847 : (cuts42847.take 1).map (fun c => (5619974145-1+2*2^10*c.k,109729006891718+c.lower,109729392905089+c.upper)) = pointBounds42847 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000088
