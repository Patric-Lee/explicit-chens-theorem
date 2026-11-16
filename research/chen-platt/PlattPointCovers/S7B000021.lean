import PlattPointSubsetKernel
import PlattPointPackets.S2B000116
import PlattPointPackets.S2B000117
import PlattPointPackets.S2B000118
import PlattPointPackets.S2B000119
import PlattPointPackets.S2B000120
import PlattGlobalGrid.S7B000021
namespace ChenEffective.PlattWindow.PointCovers.S7B000021
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000116.points ++ ChenEffective.PlattWindow.PointPackets.S2B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000118.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000120.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000021.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000021.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000021
