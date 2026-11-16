import PlattAssemblyKernel
import PlattCertificates.Count131072.C064896
import PlattCertificates.Count131072.C064897
import PlattCertificates.Count131072.C064898
import PlattCertificates.Count131072.C064899
import PlattCertificates.Count131072.C064900
import PlattCertificates.Count131072.C064901
import PlattCertificates.Count131072.C064902
import PlattCertificates.Count131072.C064903
import PlattCertificates.Count131072.C064904
import PlattCertificates.Count131072.C064905
import PlattCertificates.Count131072.C064906
import PlattCertificates.Count131072.C064907
import PlattCertificates.Count131072.C064908
import PlattCertificates.Count131072.C064909
import PlattCertificates.Count131072.C064910
import PlattCertificates.Count131072.C064911
import PlattCertificates.Count131072.C064912
import PlattCertificates.Count131072.C064913
import PlattCertificates.Count131072.C064914
import PlattCertificates.Count131072.C064915
import PlattCertificates.Count131072.C064916
import PlattCertificates.Count131072.C064917
import PlattCertificates.Count131072.C064918
import PlattCertificates.Count131072.C064919
import PlattCertificates.Count131072.C064920
import PlattCertificates.Count131072.C064921
import PlattCertificates.Count131072.C064922
import PlattCertificates.Count131072.C064923
import PlattCertificates.Count131072.C064924
import PlattCertificates.Count131072.C064925
import PlattCertificates.Count131072.C064926
import PlattCertificates.Count131072.C064927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64896 : List PrefixCut := [⟨64,189423964,189424072⟩]
theorem checked64896 : checkPrefixCuts (2^48) 8509980673 10 Manual.Count131072.C064896.packed 64 cuts64896 = true := by
 decide +kernel
def cuts64897 : List PrefixCut := [⟨12,34695989,34696010⟩,
⟨64,188329557,188329675⟩]
theorem checked64897 : checkPrefixCuts (2^48) 8510111745 10 Manual.Count131072.C064897.packed 64 cuts64897 = true := by
 decide +kernel
def pointBounds64897 : List (Nat × Nat × Nat) := [(8510136320,114883926172379,114884315135170)]
theorem point_links_checked64897 : (cuts64897.take 1).map (fun c => (8510111745-1+2*2^10*c.k,114883891476390+c.lower,114884280439160+c.upper)) = pointBounds64897 := by
 decide +kernel
def cuts64898 : List PrefixCut := [⟨64,188690496,188690609⟩]
theorem checked64898 : checkPrefixCuts (2^48) 8510242817 10 Manual.Count131072.C064898.packed 64 cuts64898 = true := by
 decide +kernel
def cuts64899 : List PrefixCut := [⟨14,41375914,41375940⟩,
⟨64,190969677,190969789⟩]
theorem checked64899 : checkPrefixCuts (2^48) 8510373889 10 Manual.Count131072.C064899.packed 64 cuts64899 = true := by
 decide +kernel
def pointBounds64899 : List (Nat × Nat × Nat) := [(8510402560,114884309872357,114884698835384)]
theorem point_links_checked64899 : (cuts64899.take 1).map (fun c => (8510373889-1+2*2^10*c.k,114884268496443+c.lower,114884657459444+c.upper)) = pointBounds64899 := by
 decide +kernel
def cuts64900 : List PrefixCut := [⟨64,188420097,188420206⟩]
theorem checked64900 : checkPrefixCuts (2^48) 8510504961 10 Manual.Count131072.C064900.packed 64 cuts64900 = true := by
 decide +kernel
def cuts64901 : List PrefixCut := [⟨16,47559329,47559354⟩,
⟨64,188714854,188714959⟩]
theorem checked64901 : checkPrefixCuts (2^48) 8510636033 10 Manual.Count131072.C064901.packed 64 cuts64901 = true := by
 decide +kernel
def pointBounds64901 : List (Nat × Nat × Nat) := [(8510668800,114884695445546,114885084408793)]
theorem point_links_checked64901 : (cuts64901.take 1).map (fun c => (8510636033-1+2*2^10*c.k,114884647886217+c.lower,114885036849439+c.upper)) = pointBounds64901 := by
 decide +kernel
def cuts64902 : List PrefixCut := [⟨64,194466575,194466686⟩]
theorem checked64902 : checkPrefixCuts (2^48) 8510767105 10 Manual.Count131072.C064902.packed 64 cuts64902 = true := by
 decide +kernel
def cuts64903 : List PrefixCut := [⟨18,52485607,52485640⟩,
⟨64,189469685,189469794⟩]
theorem checked64903 : checkPrefixCuts (2^48) 8510898177 10 Manual.Count131072.C064903.packed 64 cuts64903 = true := by
 decide +kernel
def pointBounds64903 : List (Nat × Nat × Nat) := [(8510935040,114885083553253,114885472516724)]
theorem point_links_checked64903 : (cuts64903.take 1).map (fun c => (8510898177-1+2*2^10*c.k,114885031067646+c.lower,114885420031084+c.upper)) = pointBounds64903 := by
 decide +kernel
def cuts64904 : List PrefixCut := [⟨64,188573838,188573948⟩]
theorem checked64904 : checkPrefixCuts (2^48) 8511029249 10 Manual.Count131072.C064904.packed 64 cuts64904 = true := by
 decide +kernel
def cuts64905 : List PrefixCut := [⟨20,60553353,60553387⟩,
⟨64,192473318,192473432⟩]
theorem checked64905 : checkPrefixCuts (2^48) 8511160321 10 Manual.Count131072.C064905.packed 64 cuts64905 = true := by
 decide +kernel
def pointBounds64905 : List (Nat × Nat × Nat) := [(8511201280,114885469664522,114885858628213)]
theorem point_links_checked64905 : (cuts64905.take 1).map (fun c => (8511160321-1+2*2^10*c.k,114885409111169+c.lower,114885798074826+c.upper)) = pointBounds64905 := by
 decide +kernel
def cuts64906 : List PrefixCut := [⟨64,189758572,189758675⟩]
theorem checked64906 : checkPrefixCuts (2^48) 8511291393 10 Manual.Count131072.C064906.packed 64 cuts64906 = true := by
 decide +kernel
def cuts64907 : List PrefixCut := [⟨22,66338752,66338789⟩,
⟨64,189193483,189193583⟩]
theorem checked64907 : checkPrefixCuts (2^48) 8511422465 10 Manual.Count131072.C064907.packed 64 cuts64907 = true := by
 decide +kernel
def pointBounds64907 : List (Nat × Nat × Nat) := [(8511467520,114885857681811,114886246645722)]
theorem point_links_checked64907 : (cuts64907.take 1).map (fun c => (8511422465-1+2*2^10*c.k,114885791343059+c.lower,114886180306933+c.upper)) = pointBounds64907 := by
 decide +kernel
def cuts64908 : List PrefixCut := [⟨64,192695911,192696023⟩]
theorem checked64908 : checkPrefixCuts (2^48) 8511553537 10 Manual.Count131072.C064908.packed 64 cuts64908 = true := by
 decide +kernel
def cuts64909 : List PrefixCut := [⟨24,70007368,70007410⟩,
⟨64,188030212,188030323⟩]
theorem checked64909 : checkPrefixCuts (2^48) 8511684609 10 Manual.Count131072.C064909.packed 64 cuts64909 = true := by
 decide +kernel
def pointBounds64909 : List (Nat × Nat × Nat) := [(8511733760,114886243239821,114886632203949)]
theorem point_links_checked64909 : (cuts64909.take 1).map (fun c => (8511684609-1+2*2^10*c.k,114886173232453+c.lower,114886562196539+c.upper)) = pointBounds64909 := by
 decide +kernel
def cuts64910 : List PrefixCut := [⟨64,186902995,186903106⟩]
theorem checked64910 : checkPrefixCuts (2^48) 8511815681 10 Manual.Count131072.C064910.packed 64 cuts64910 = true := by
 decide +kernel
def cuts64911 : List PrefixCut := [⟨26,76618818,76618862⟩,
⟨64,186966258,186966365⟩]
theorem checked64911 : checkPrefixCuts (2^48) 8511946753 10 Manual.Count131072.C064911.packed 64 cuts64911 = true := by
 decide +kernel
def pointBounds64911 : List (Nat × Nat × Nat) := [(8512000000,114886624784478,114887013748830)]
theorem point_links_checked64911 : (cuts64911.take 1).map (fun c => (8511946753-1+2*2^10*c.k,114886548165660+c.lower,114886937129968+c.upper)) = pointBounds64911 := by
 decide +kernel
def cuts64912 : List PrefixCut := [⟨64,191460563,191460672⟩]
theorem checked64912 : checkPrefixCuts (2^48) 8512077825 10 Manual.Count131072.C064912.packed 64 cuts64912 = true := by
 decide +kernel
def cuts64913 : List PrefixCut := [⟨28,82932249,82932297⟩,
⟨64,188018644,188018753⟩]
theorem checked64913 : checkPrefixCuts (2^48) 8512208897 10 Manual.Count131072.C064913.packed 64 cuts64913 = true := by
 decide +kernel
def pointBounds64913 : List (Nat × Nat × Nat) := [(8512266240,114887009524730,114887398489302)]
theorem point_links_checked64913 : (cuts64913.take 1).map (fun c => (8512208897-1+2*2^10*c.k,114886926592481+c.lower,114887315557005+c.upper)) = pointBounds64913 := by
 decide +kernel
def cuts64914 : List PrefixCut := [⟨64,192711186,192711296⟩]
theorem checked64914 : checkPrefixCuts (2^48) 8512339969 10 Manual.Count131072.C064914.packed 64 cuts64914 = true := by
 decide +kernel
def cuts64915 : List PrefixCut := [⟨30,90138081,90138134⟩,
⟨64,191021852,191021962⟩]
theorem checked64915 : checkPrefixCuts (2^48) 8512471041 10 Manual.Count131072.C064915.packed 64 cuts64915 = true := by
 decide +kernel
def pointBounds64915 : List (Nat × Nat × Nat) := [(8512532480,114887397460392,114887786425188)]
theorem point_links_checked64915 : (cuts64915.take 1).map (fun c => (8512471041-1+2*2^10*c.k,114887307322311+c.lower,114887696287054+c.upper)) = pointBounds64915 := by
 decide +kernel
def cuts64916 : List PrefixCut := [⟨64,190357589,190357697⟩]
theorem checked64916 : checkPrefixCuts (2^48) 8512602113 10 Manual.Count131072.C064916.packed 64 cuts64916 = true := by
 decide +kernel
def cuts64917 : List PrefixCut := [⟨32,96020855,96020909⟩,
⟨64,189726444,189726547⟩]
theorem checked64917 : checkPrefixCuts (2^48) 8512733185 10 Manual.Count131072.C064917.packed 64 cuts64917 = true := by
 decide +kernel
def pointBounds64917 : List (Nat × Nat × Nat) := [(8512798720,114887784722607,114888173687622)]
theorem point_links_checked64917 : (cuts64917.take 1).map (fun c => (8512733185-1+2*2^10*c.k,114887688701752+c.lower,114888077666713+c.upper)) = pointBounds64917 := by
 decide +kernel
def cuts64918 : List PrefixCut := [⟨64,189062227,189062343⟩]
theorem checked64918 : checkPrefixCuts (2^48) 8512864257 10 Manual.Count131072.C064918.packed 64 cuts64918 = true := by
 decide +kernel
def cuts64919 : List PrefixCut := [⟨34,101142798,101142857⟩,
⟨64,187935154,187935260⟩]
theorem checked64919 : checkPrefixCuts (2^48) 8512995329 10 Manual.Count131072.C064919.packed 64 cuts64919 = true := by
 decide +kernel
def pointBounds64919 : List (Nat × Nat × Nat) := [(8513064960,114888168633221,114888557598460)]
theorem point_links_checked64919 : (cuts64919.take 1).map (fun c => (8512995329-1+2*2^10*c.k,114888067490423+c.lower,114888456455603+c.upper)) = pointBounds64919 := by
 decide +kernel
def cuts64920 : List PrefixCut := [⟨64,187766929,187767037⟩]
theorem checked64920 : checkPrefixCuts (2^48) 8513126401 10 Manual.Count131072.C064920.packed 64 cuts64920 = true := by
 decide +kernel
def cuts64921 : List PrefixCut := [⟨36,105404787,105404847⟩,
⟨64,188788992,188789098⟩]
theorem checked64921 : checkPrefixCuts (2^48) 8513257473 10 Manual.Count131072.C064921.packed 64 cuts64921 = true := by
 decide +kernel
def pointBounds64921 : List (Nat × Nat × Nat) := [(8513331200,114888548597293,114888937562747)]
theorem point_links_checked64921 : (cuts64921.take 1).map (fun c => (8513257473-1+2*2^10*c.k,114888443192506+c.lower,114888832157900+c.upper)) = pointBounds64921 := by
 decide +kernel
def cuts64922 : List PrefixCut := [⟨64,188521593,188521704⟩]
theorem checked64922 : checkPrefixCuts (2^48) 8513388545 10 Manual.Count131072.C064922.packed 64 cuts64922 = true := by
 decide +kernel
def cuts64923 : List PrefixCut := [⟨38,110856738,110856806⟩,
⟨64,189113786,189113897⟩]
theorem checked64923 : checkPrefixCuts (2^48) 8513519617 10 Manual.Count131072.C064923.packed 64 cuts64923 = true := by
 decide +kernel
def pointBounds64923 : List (Nat × Nat × Nat) := [(8513597440,114888931359829,114889320325508)]
theorem point_links_checked64923 : (cuts64923.take 1).map (fun c => (8513519617-1+2*2^10*c.k,114888820503091+c.lower,114889209468702+c.upper)) = pointBounds64923 := by
 decide +kernel
def cuts64924 : List PrefixCut := [⟨64,189110894,189111005⟩]
theorem checked64924 : checkPrefixCuts (2^48) 8513650689 10 Manual.Count131072.C064924.packed 64 cuts64924 = true := by
 decide +kernel
def cuts64925 : List PrefixCut := [⟨40,118060577,118060644⟩,
⟨64,187487994,187488100⟩]
theorem checked64925 : checkPrefixCuts (2^48) 8513781761 10 Manual.Count131072.C064925.packed 64 cuts64925 = true := by
 decide +kernel
def pointBounds64925 : List (Nat × Nat × Nat) := [(8513863680,114889316788348,114889705754248)]
theorem point_links_checked64925 : (cuts64925.take 1).map (fun c => (8513781761-1+2*2^10*c.k,114889198727771+c.lower,114889587693604+c.upper)) = pointBounds64925 := by
 decide +kernel
def cuts64926 : List PrefixCut := [⟨64,190196056,190196163⟩]
theorem checked64926 : checkPrefixCuts (2^48) 8513912833 10 Manual.Count131072.C064926.packed 64 cuts64926 = true := by
 decide +kernel
def cuts64927 : List PrefixCut := [⟨42,124999503,124999574⟩,
⟨64,191085744,191085852⟩]
theorem checked64927 : checkPrefixCuts (2^48) 8514043905 10 Manual.Count131072.C064927.packed 64 cuts64927 = true := by
 decide +kernel
def pointBounds64927 : List (Nat × Nat × Nat) := [(8514129920,114889701411324,114890090377441)]
theorem point_links_checked64927 : (cuts64927.take 1).map (fun c => (8514043905-1+2*2^10*c.k,114889576411821+c.lower,114889965377867+c.upper)) = pointBounds64927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000153
