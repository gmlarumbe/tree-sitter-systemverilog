        begin
            requested_channel_is_available =
            |(request[N][NS-1:0]& ~sgrant & ~requested[N][NS-1:0]);

            if (request[N][NS])
                requested_channel_is_available = 1;

            if (NM < 2)
                requested_channel_is_available = m_stb[N];
        end
