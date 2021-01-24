library(scales)
library(tidyverse)
library(readr)

is_bitter <- Vectorize(function(fn) {
  switch(fn,
         "bitter-checked" = TRUE,
         "bitter-unchecked" = TRUE,
         FALSE)
})

get_line_type <- Vectorize(function(fn) {
  switch(fn,
         "bitter-checked" = "bitter",
         "bitter-unchecked" = "bitter",
         "other")
})

df <- read_csv("./benchmark-data.csv")

df <- mutate(df,
             fn = `function`,
             bitter = is_bitter(fn),
             line = get_line_type(fn),
             latency = (iteration_count * 10000) / sample_measured_value,
)

ggplot(df, aes(value, latency, color = fn)) +
  stat_summary(fun = mean, geom="point", size = 1.5) +
  stat_summary(aes(linetype = line), fun = mean, geom="line", size = 1.2) +
  scale_y_continuous(breaks = pretty_breaks(10)) +
  scale_x_continuous(limit = c(1, NA), breaks = pretty_breaks(12)) +
  labs(title = "Rust Bit Readers Performance Comparison",
       subtitle = "Performance measured in reads per nanosecond (higher is better)",
       caption = "Bitter implementations marked with solid lines",
       col = "Bit reader",
       y = "Reads per ns",
       x = "Read size (bits)") +
  guides(linetype = FALSE)
ggsave('bench-bit-reads.png', width = 9, height = 5, dpi = 100)
