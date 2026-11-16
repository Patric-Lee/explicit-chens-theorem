import PlattPointSubsetKernel
import PlattPointPackets.S2B000141
import PlattPointPackets.S2B000142
import PlattPointPackets.S2B000143
import PlattPointPackets.S2B000144
import PlattPointPackets.S2B000145
import PlattGlobalGrid.S7B000028
namespace ChenEffective.PlattWindow.PointCovers.S7B000028
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000141.points ++ ChenEffective.PlattWindow.PointPackets.S2B000142.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000143.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000144.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000145.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000028.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000028.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000028
