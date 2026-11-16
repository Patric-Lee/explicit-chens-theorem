import PlattPointSubsetKernel
import PlattPointPackets.S2B000184
import PlattPointPackets.S2B000185
import PlattPointPackets.S2B000186
import PlattPointPackets.S2B000187
import PlattPointPackets.S2B000188
import PlattGlobalGrid.S7B000039
namespace ChenEffective.PlattWindow.PointCovers.S7B000039
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000184.points ++ ChenEffective.PlattWindow.PointPackets.S2B000185.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000186.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000187.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000188.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000039.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000039.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000039
